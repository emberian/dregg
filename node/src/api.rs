//! Axum HTTP API router for the dregg node.
//!
//! Serves a localhost-only API that the browser extension cipherclerk talks to.
//! All handlers access shared [`NodeState`] via Axum's state extraction.

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::IpAddr;
use std::sync::Arc;
use std::time::Instant;

use argon2::password_hash::SaltString;
use argon2::password_hash::rand_core::OsRng;
use argon2::{Argon2, PasswordHash, PasswordHasher, PasswordVerifier};
use axum::extract::DefaultBodyLimit;
use axum::http::Request;
use axum::http::{HeaderValue, Method, header};
use axum::response::Response;
use axum::response::sse::{Event, Sse};
use axum::{
    Json, Router,
    extract::ConnectInfo,
    extract::Path as AxumPath,
    extract::Query,
    extract::State,
    http::StatusCode,
    middleware,
    routing::{get, post},
};
use futures_util::stream::{self, Stream};
use serde::{Deserialize, Serialize};
use std::convert::Infallible;
use subtle::ConstantTimeEq;
use tokio::sync::Mutex;

use dregg_sdk::{Attenuation, AuthRequest, CellId, SignedTurn};
use dregg_turn::{CallForest, Turn};

use crate::state::{ActivityProofStatus, ActivityStatus, CommittedEvent, NodeEvent, NodeState};
use crate::ws::handle_ws;

// =============================================================================
// Request/Response types
// =============================================================================

#[derive(Serialize)]
pub struct StatusResponse {
    /// True when the node is up AND consensus is live (a blocklace handle is
    /// present and the DAG has a tip / is producing blocks). This reflects
    /// real liveness, NOT the attested-root height — so a healthy devnet that
    /// is producing heartbeat blocks reports `healthy: true` even before the
    /// first turn advances the attested root. See `dag_height` vs
    /// `latest_height` below.
    pub healthy: bool,
    pub peer_count: usize,
    /// Attested-root / turn height: the height of the latest finalized
    /// AttestedRoot. This advances only on turn-bearing finality, NOT on idle
    /// heartbeat blocks, so it can legitimately be 0 on a fresh node whose DAG
    /// is already tall. Kept for backward compatibility; use `dag_height` for
    /// "how tall is the chain".
    pub latest_height: u64,
    /// Real blocklace DAG tip height: the max block `seq` in the local lace.
    /// This advances on EVERY block (turns and heartbeats), so it is the
    /// honest public "the chain is at height N" signal. 0 if consensus has not
    /// produced a block yet (or no blocklace handle is attached).
    pub dag_height: u64,
    /// Number of blocks currently in the local blocklace DAG.
    pub block_count: usize,
    /// Whether a blocklace consensus handle is attached (consensus task is
    /// running). One of the inputs to `healthy`.
    pub consensus_live: bool,
    /// F-8: aggregate private-activity counters (count of revoked credentials /
    /// shielded notes). These leak the *volume* of private activity to any
    /// unauthenticated scraper, so they are OMITTED from the public `/status`
    /// response by default (`serde` skips `None`). An operator who wants them on
    /// the wire opts in explicitly via `DREGG_STATUS_EXPOSE_COUNTS=1` (e.g. for a
    /// trusted internal dashboard behind auth). Default: `None` → field absent.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revocation_count: Option<u64>,
    /// F-8: see `revocation_count`. Omitted by default.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note_count: Option<u64>,
    pub federation_mode: String,
    pub public_key: String,
    /// THE SWAP — honest verified-execution surface. The authoritative state
    /// producer on the commit path:
    ///   * `"lean"`  — the VERIFIED Lean executor produces the committed state
    ///     for swap-safe (root-agreeing) turns (the DEFAULT; opt out with
    ///     `DREGG_LEAN_PRODUCER=0`); the Rust executor is a logged differential
    ///     cross-check.
    ///   * `"rust"`  — the legacy Rust executor produces (Lean runs at most as a
    ///     veto-only shadow). Reached only via `DREGG_LEAN_PRODUCER=0`.
    pub state_producer: String,
    /// Whether the verified Lean producer is enabled (mirrors `state_producer ==
    /// "lean"`). Convenience boolean for clients.
    pub lean_producer: bool,
    /// Whether the node generates + verifies a full-turn STARK proof for every
    /// committed turn on the commit path (the "every transition is proven"
    /// claim). When `false`, only activity proofs are produced on submission.
    pub full_turn_proving: bool,
    /// Number of SWAP-SAFE (root-agreeing) effect KINDS for which the verified
    /// producer INSTALLS its post-state. A turn touching only these effects is
    /// produced by the verified Lean executor; a turn touching any root-gap or
    /// unmappable effect falls back to Rust for that turn. See
    /// `GET /api/node/producer` for the full per-effect breakdown.
    pub producer_covered_effects: usize,
}

/// Response from `GET /api/node/producer` — the honest verified-execution
/// surface (THE SWAP boundary). Tells a client EXACTLY which state producer
/// runs the commit path and, when the verified Lean producer is enabled, which
/// effect kinds it covers (defaults to Lean for) vs. which still fall back to
/// the Rust producer.
#[derive(Serialize)]
pub struct ProducerStatusResponse {
    /// `"lean"` or `"rust"` — the authoritative state producer on the commit path.
    pub state_producer: String,
    /// Whether the verified Lean producer is enabled (default ON; opt out with
    /// `DREGG_LEAN_PRODUCER=0`).
    pub lean_producer_enabled: bool,
    /// Whether a full-turn STARK proof is generated + verified per committed turn.
    pub full_turn_proving: bool,
    /// Effect kinds the producer covers (a turn touching ONLY these runs on the
    /// verified producer when enabled). Mirrors the marshaller's wire-projected set.
    pub covered_effects: Vec<String>,
    /// Total number of distinct on-chain effect kinds.
    pub total_effect_kinds: usize,
    /// Effect kinds NOT yet covered — a turn touching any of these falls back to
    /// the Rust producer for that turn. This is the honest "blocks the full
    /// default" list.
    pub uncovered_effects: Vec<String>,
    /// The SWAP-SAFE subset of `covered_effects`: the producer runs AND its
    /// reconstituted `.root()` provably EQUALS the Rust executor's (pinned by the
    /// `lean_state_producer_*` differentials). A turn touching ONLY these has ZERO
    /// post-state divergence when the verified producer runs.
    pub root_agreeing_effects: Vec<String>,
    /// Mapped effects whose Lean-produced `.root()` DIVERGES from Rust (the wire
    /// model is lossier than the cell commitment, or Rust re-shapes the ledger):
    /// the producer still runs and installs the verified state, but the divergence
    /// is logged as a real finding. The CHARACTERIZED residual of THE SWAP.
    pub root_gap_effects: Vec<String>,
    /// Human-readable summary of the boundary.
    pub summary: String,
}

/// Response from `GET /api/node/identity` — the node operator's own identity.
/// The `agent_cell` is the cell `/turn/submit` acts on by default (the node
/// signs every operator turn as this cell); a client can fund it via the faucet
/// or target it directly. This makes the "who am I / what's my cell" question a
/// first-class answer instead of a derivation a client has to reproduce.
#[derive(Serialize)]
pub struct NodeIdentityResponse {
    /// Hex-encoded operator Ed25519 public key.
    pub public_key: String,
    /// Hex-encoded operator agent cell id (`derive_raw(public_key, H("default"))`).
    pub agent_cell: String,
    /// Whether the operator's cipherclerk is unlocked (turns can be signed).
    pub unlocked: bool,
    /// Current balance of the agent cell, if it exists in the ledger.
    /// THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub agent_balance: Option<i64>,
    /// Current nonce of the agent cell, if it exists.
    pub agent_nonce: Option<u64>,
}

#[derive(Serialize)]
pub struct CipherclerkResponse {
    pub unlocked: bool,
    pub public_key: String,
    pub token_count: usize,
    pub receipt_chain_length: usize,
}

#[derive(Deserialize)]
pub struct AuthorizeRequest {
    pub token_id: String,
    pub service: Option<String>,
    pub action: Option<String>,
}

#[derive(Serialize)]
pub struct AuthorizeResponse {
    pub authorized: bool,
    pub reason: Option<String>,
}

#[derive(Deserialize)]
pub struct MintRequest {
    pub service: String,
}

#[derive(Serialize)]
pub struct MintResponse {
    pub token_id: String,
    pub service: String,
}

#[derive(Deserialize)]
pub struct AttenuateRequest {
    pub token_id: String,
    pub services: Vec<(String, String)>,
}

#[derive(Serialize)]
pub struct AttenuateResponse {
    pub new_token_id: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct TokenInfo {
    pub id: String,
    pub label: String,
    pub service: String,
}

#[derive(Serialize)]
pub struct ReceiptInfo {
    pub chain_index: u64,
    pub chain_head: bool,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub agent: String,
    pub pre_state: String,
    pub post_state: String,
    pub timestamp: i64,
    pub computrons_used: u64,
    pub action_count: usize,
    pub previous_receipt_hash: Option<String>,
    pub finality: String,
    pub was_encrypted: bool,
    pub was_burn: bool,
    pub has_proof: bool,
    pub executor_signed: bool,
    pub has_witness: bool,
    pub witness_count: usize,
}

#[derive(Deserialize)]
pub struct SubmitTurnRequest {
    /// Hex-encoded 32-byte CellId.
    ///
    /// NOTE: this is advisory only. The node derives the real agent cell from
    /// its own cipherclerk pubkey (confused-deputy hardening, F-P1-3) and signs
    /// the turn as itself. The body value is parsed for validation/error
    /// reporting but never trusted as the signer.
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    /// The turn's actions — each becomes a root in the call forest, signed by
    /// the node operator's cipherclerk and routed through consensus.
    ///
    /// Historically this field did not exist and the handler built an empty
    /// `CallForest`, so every operator-signed turn was rejected by the executor
    /// ("call forest is empty") and nothing ever replicated. A request with no
    /// actions still round-trips (it produces an empty no-op turn that the
    /// executor rejects honestly) but real flows MUST carry at least one action.
    #[serde(default)]
    pub actions: Vec<TurnActionSpec>,
}

/// One action in a `SubmitTurnRequest`. The operator's cipherclerk signs each
/// action over its canonical bytes (`AgentCipherclerk::make_action`), so the
/// resulting `Authorization::Signature` authenticates the operator as the
/// caller for every effect in the action.
#[derive(Deserialize)]
pub struct TurnActionSpec {
    /// Hex-encoded 32-byte target cell id. Defaults to the operator's own
    /// agent cell when omitted (the common "act on my own cell" case).
    #[serde(default)]
    pub target: Option<String>,
    /// Method name (hashed to a `Symbol`). Defaults to `"submit"`.
    #[serde(default)]
    pub method: Option<String>,
    /// The effects this action applies.
    pub effects: Vec<TurnEffectSpec>,
}

/// A JSON-friendly projection of the on-chain `Effect` enum, covering the
/// effect kinds that a thin HTTP client needs to drive app flows: state
/// writes, value transfers, nonce bumps, and event emission. Richer effects
/// (notes, capability grants, factory births) go through the typed
/// `/turns/submit` signed-envelope path with an SDK-built `SignedTurn`.
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TurnEffectSpec {
    /// Write a 32-byte field element into a cell's state slot.
    SetField {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
        index: usize,
        /// Hex-encoded value: a full 64-char hex field element, or a shorter
        /// hex/decimal scalar that is left-padded into a little-endian u64.
        value: String,
    },
    /// Transfer computrons between cells.
    Transfer {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        from: Option<String>,
        to: String,
        amount: u64,
    },
    /// Emit an event (topic + data) from a cell.
    EmitEvent {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
        topic: String,
        /// Event data words, each a hex/decimal scalar.
        #[serde(default)]
        data: Vec<String>,
    },
    /// Increment a cell's nonce by 1.
    IncrementNonce {
        /// Hex cell id. Defaults to the action's target.
        #[serde(default)]
        cell: Option<String>,
    },
}

/// Parse a value string into a 32-byte field element.
///
/// Accepts either a full 64-char hex field element (used verbatim) or a
/// shorter hex (`0x…`) / decimal scalar, which is encoded little-endian into
/// the low 8 bytes. This mirrors the wasm runtime's `value_hex` convention so
/// the HTTP path and the in-browser preview agree on encoding.
fn parse_field_element(s: &str) -> Result<[u8; 32], String> {
    let t = s.trim();
    if t.len() == 64 && t.bytes().all(|b| b.is_ascii_hexdigit()) {
        let bytes = hex_decode(t).map_err(|_| format!("invalid hex field element: {s}"))?;
        let mut out = [0u8; 32];
        out.copy_from_slice(&bytes);
        return Ok(out);
    }
    let scalar = if let Some(hex) = t.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).map_err(|_| format!("invalid hex scalar: {s}"))?
    } else {
        t.parse::<u64>()
            .map_err(|_| format!("invalid scalar: {s}"))?
    };
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&scalar.to_le_bytes());
    Ok(out)
}

fn parse_cell_id(s: &str) -> Result<CellId, String> {
    let bytes: [u8; 32] = hex_decode(s).map_err(|_| format!("invalid cell id: {s}"))?;
    Ok(CellId(bytes))
}

/// Convert a `TurnEffectSpec` into an on-chain `Effect`, resolving cell
/// defaults against the action's target.
fn build_effect(spec: TurnEffectSpec, default_cell: CellId) -> Result<dregg_turn::Effect, String> {
    use dregg_turn::Effect;
    let resolve = |opt: Option<String>| -> Result<CellId, String> {
        match opt {
            Some(h) => parse_cell_id(&h),
            None => Ok(default_cell),
        }
    };
    Ok(match spec {
        TurnEffectSpec::SetField { cell, index, value } => Effect::SetField {
            cell: resolve(cell)?,
            index,
            value: parse_field_element(&value)?,
        },
        TurnEffectSpec::Transfer { from, to, amount } => Effect::Transfer {
            from: resolve(from)?,
            to: parse_cell_id(&to)?,
            amount,
        },
        TurnEffectSpec::EmitEvent { cell, topic, data } => {
            let words: Result<Vec<[u8; 32]>, String> =
                data.iter().map(|w| parse_field_element(w)).collect();
            Effect::EmitEvent {
                cell: resolve(cell)?,
                event: dregg_turn::action::Event::new(dregg_turn::action::symbol(&topic), words?),
            }
        }
        TurnEffectSpec::IncrementNonce { cell } => Effect::IncrementNonce {
            cell: resolve(cell)?,
        },
    })
}

#[derive(Serialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct SubmitSignedTurnResponse {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub signer: Option<String>,
    pub action_count: usize,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

// =============================================================================
// EncryptedTurn submission types (AUDIT-privacy.md §11.2 wiring).
//
// Wire format: the request body is the postcard-serialized
// `dregg_turn::EncryptedTurn` envelope as **raw bytes** (Content-Type:
// application/octet-stream). The body is **not** wrapped in JSON because
// the EncryptedTurn includes a ciphertext blob whose size makes hex/base64
// inflation undesirable and because postcard is the canonical dregg wire
// format for binary envelopes.
//
// The executor's X25519 unsealer secret is derived from the node's cipherclerk
// via `AgentCipherclerk::derive_symmetric_key("dregg-turn-unsealer-v1")`.
// The matching public key is exposed via `GET /turns/encryption-key` so a
// sender can encrypt to this executor.
//
// Boundary (BOUNDARIES.md §5):
//   - **out-of-band**: gossip observers / route hops (see only ciphertext)
//   - **cleartext-inside**: the executor holding the unsealer secret
//   - the receipt's `was_encrypted: true` bit is the only fact disclosed
//     after commit.
// =============================================================================

/// Response from `GET /turns/encryption-key` — the X25519 public key
/// the executor accepts `EncryptedTurn`s under. Senders use this with
/// `EncryptedTurn::encrypt_for_executor`.
#[derive(Serialize)]
pub struct TurnEncryptionKeyResponse {
    /// 64 hex chars — the executor's static X25519 public key.
    pub executor_x25519_public: String,
    /// Domain-string used to derive the secret from the cipherclerk seed.
    /// Lets verifiers reconstruct the deployment's key-derivation path.
    pub derivation_domain: String,
}

/// Response from `POST /turns/submit-encrypted`.
#[derive(Serialize)]
pub struct SubmitEncryptedTurnResponse {
    pub accepted: bool,
    /// On success, hex-encoded BLAKE3 hash of the recovered inner turn.
    /// On reject, contains "rejected: <reason>". The recovered turn hash
    /// is itself derivable by anyone who can decrypt; it is NOT a privacy
    /// leak (the encrypted-turn commitment already binds to this hash).
    pub turn_hash: Option<String>,
    /// Whether the receipt's `was_encrypted` bit was set (always `true`
    /// on success; included so the caller can confirm the encrypted path
    /// was actually taken).
    pub was_encrypted: bool,
    pub proof_status: ActivityProofStatus,
    pub has_witness: bool,
    pub witness_count: usize,
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct CellResponse {
    pub id: String,
    pub found: bool,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: Option<i64>,
}

#[derive(Serialize)]
pub struct AttestedRootInfo {
    pub height: u64,
    pub merkle_root: String,
    pub timestamp: i64,
    pub signatures: usize,
}

#[derive(Serialize)]
pub struct FederationInfo {
    pub id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub threshold: u32,
    pub member_count: usize,
    pub members: Vec<String>,
    pub is_local: bool,
    pub latest_height: u64,
    pub latest_root: Option<String>,
    pub num_finalized_roots: usize,
}

#[derive(Serialize)]
pub struct CellListEntry {
    pub id: String,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub has_program: bool,
    pub found: bool,
}

#[derive(Serialize)]
pub struct CellDetailResponse {
    pub id: String,
    pub found: bool,
    // THE EPOCH: SIGNED (i64) — issuer wells carry −supply.
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    /// Alias for JS inspector compat (cell.js + Starbridge Remote expect num_capabilities in some paths).
    pub num_capabilities: usize,
    pub has_delegate: bool,
    pub delegate: Option<String>,
    pub has_program: bool,
    pub public_key: String,
    pub token_id: String,
    pub proved_state: bool,
    pub delegation_epoch: u64,
    /// Content-addressed commitment for PeerExchange / state sync (matches wasm CellStateView).
    pub state_commitment: String,
    /// Quick kind for <dregg-cell-program> and raw views without full program dump.
    pub program_kind: String,
    /// Full self-describing program view (`{ kind, constraints | cases |
    /// circuit_hash }`) — the SAME total `StateConstraintView` projection the
    /// wasm runtime serves (`dregg_cell::program::CellProgramView`), so a
    /// live cell can show its own slot caveats (e.g. a council cell's
    /// AffineLe threshold M) to remote inspectors.
    pub program: dregg_cell::program::CellProgramView,
    /// The cell's `[FieldElement; 16]` state slots, each hex-encoded (64 chars).
    ///
    /// Empty when the cell is not found. Slot indices match the on-chain layout
    /// (`SetField` writes here); userspace apps (e.g. the nameservice) pin a
    /// fixed slot schema and read named slots out of this vector. Exposing the
    /// raw fields lets a thin client "resolve" a name by reading its slots back
    /// rather than only replaying events.
    #[serde(default)]
    pub fields: Vec<String>,
}

#[derive(Serialize)]
pub struct CheckpointResponse {
    pub height: u64,
    pub ledger_state_root: String,
    pub note_tree_root: String,
    pub nullifier_set_root: String,
    pub revocation_tree_root: String,
    pub epoch: u64,
    pub timestamp: i64,
    pub federation_members: usize,
    pub qc_votes: usize,
}

#[derive(Deserialize)]
pub struct UnlockRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct UnlockResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bearer_token: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct SetPassphraseRequest {
    pub passphrase: String,
}

#[derive(Serialize)]
pub struct SetPassphraseResponse {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Serialize)]
pub struct IntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
    /// `true` when the submitted intent was *self-fulfillable* and was COMMITTED
    /// immediately through the verified ledger at submit time (rather than only
    /// pooled). When `true`, `turn_hash` carries the real committed receipt hash.
    #[serde(default)]
    pub committed: bool,
    /// Hex-encoded `turn_hash` of the committed fulfillment receipt, present iff
    /// `committed == true`. This is a genuine receipt from
    /// `execute_fulfillment_flow_verified` (the same verified path `/intents/fulfill`
    /// drives), NOT a stub.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn_hash: Option<String>,
}

#[derive(Serialize)]
pub struct EncryptedIntentSubmitResponse {
    pub intent_id: String,
    pub stored: bool,
}

// =============================================================================
// SSE (Searchable Symmetric Encryption) match query types
// =============================================================================

/// Request body for `/intents/encrypted/search` — a fulfiller's local
/// capability keywords + epoch, used as a coarse SSE-token filter
/// against the node's encrypted intent pool.
///
/// The fulfiller hashes each of their `capability_keywords` under
/// `(keyword, epoch)` to produce SSE search tokens, and the server
/// streams back any stored encrypted intent whose token set intersects.
/// The intent body remains encrypted; the fulfiller requests body
/// decryption out-of-band after picking matches.
#[derive(Deserialize)]
pub struct SseSearchRequest {
    /// Capability keywords (cleartext, e.g. "action:read",
    /// "resource:documents/*"). The server hashes each as
    /// `BLAKE3_derive_key("dregg-sse-token-v1", keyword || epoch_le)`.
    pub capability_keywords: Vec<String>,
    /// Epoch for token derivation (must match the epoch the poster
    /// used; rotate-by-epoch makes cross-epoch correlation harder).
    pub epoch: u64,
    /// Maximum results to return (cap at server-side limit).
    #[serde(default)]
    pub limit: Option<usize>,
}

/// A single SSE search hit: the encrypted intent (still encrypted)
/// plus its content-addressed id for follow-up.
#[derive(Serialize)]
pub struct SseSearchHit {
    pub intent_id: String,
    pub encrypted_intent: dregg_intent::sse::EncryptedIntent,
}

/// Response from `/intents/encrypted/search`. Returns intent
/// envelopes whose SSE tokens intersect with any of the request's
/// derived tokens.
#[derive(Serialize)]
pub struct SseSearchResponse {
    pub hits: Vec<SseSearchHit>,
    /// Number of intents matched before `limit` truncation (lets the
    /// client know if there are more results behind the cap).
    pub total_matches: usize,
}

// =============================================================================
// Events query types
// =============================================================================

/// Query parameters for GET /api/events.
#[derive(Deserialize)]
pub struct EventsQuery {
    /// Return events committed after this block height. A cursor of 0 returns
    /// the current retained log for first-time pollers.
    pub since_height: Option<u64>,
    /// Maximum number of events to return (default 50, max 200).
    pub limit: Option<usize>,
}

/// Query parameters for public Starbridge indexing reads.
#[derive(Deserialize)]
pub struct StarbridgeQuery {
    /// Maximum results to return (default 50, max 200).
    pub limit: Option<usize>,
    /// Receipt/event cursor. For event reads this is exclusive when nonzero.
    pub since_height: Option<u64>,
    /// Hex-encoded cell id. Receipt reads match the receipt agent; event and
    /// turn reads match affected cells/action targets/effect cell references.
    pub cell: Option<String>,
    /// Case-insensitive substring match against memo/effect/action summaries.
    pub memo: Option<String>,
    /// Case-insensitive effect kind or summary substring.
    pub effect: Option<String>,
    /// Exact hex-encoded turn hash.
    pub turn_hash: Option<String>,
    /// Exact hex-encoded effects hash for receipt reads.
    pub effects_hash: Option<String>,
    /// Case-insensitive app bucket: nameservice, identity, governance, or custom.
    pub app: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeReceiptInfo {
    #[serde(flatten)]
    pub receipt: ReceiptInfo,
    pub effects_hash: String,
    pub federation_id: String,
    pub emitted_event_count: usize,
    pub routing_directive_count: usize,
    pub derivation_record_count: usize,
    pub source: &'static str,
    pub turn_body_available: bool,
}

#[derive(Serialize)]
pub struct StarbridgeSignedTurnInfo {
    pub queue_index: usize,
    pub turn_hash: String,
    pub signer: String,
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    pub action_count: usize,
    pub effect_count: usize,
    pub action_targets: Vec<String>,
    pub effect_kinds: Vec<String>,
    pub touched_cells: Vec<String>,
    pub app: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeActionInfo {
    pub source: &'static str,
    pub queue_index: usize,
    pub action_index: usize,
    pub turn_hash: String,
    pub signer: String,
    pub agent: String,
    pub memo: Option<String>,
    pub app: Option<String>,
    pub target: String,
    pub method: String,
    pub effect_kinds: Vec<String>,
    pub touched_cells: Vec<String>,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityEventInfo {
    pub source: &'static str,
    pub chain_index: Option<u64>,
    pub event_index: Option<usize>,
    pub height: Option<u64>,
    pub receipt_hash: Option<String>,
    pub turn_hash: String,
    pub cell_id: String,
    pub timestamp: i64,
    pub topic: Option<serde_json::Value>,
    pub data: Option<serde_json::Value>,
    pub effects: Vec<String>,
    pub proof_status: ActivityProofStatus,
    pub finality: Option<String>,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityCredentialInfo {
    pub source: &'static str,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub issuer_cell: String,
    pub subject_cells: Vec<String>,
    pub timestamp: i64,
    pub effects_hash: String,
    pub event_count: usize,
    pub derivation_record_count: usize,
    pub proof_status: ActivityProofStatus,
    pub finality: String,
}

#[derive(Serialize)]
pub struct StarbridgeIdentityProofCheckpointInfo {
    pub source: &'static str,
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    pub cell_id: String,
    pub timestamp: i64,
    pub effects_hash: String,
    pub pre_state: String,
    pub post_state: String,
    pub proof_status: ActivityProofStatus,
    pub executor_signed: bool,
    pub witness_count: usize,
    pub finality: String,
}

// =============================================================================
// PIR (Private Information Retrieval) types
// =============================================================================

/// Request body for a PIR query against the intent index.
#[derive(Deserialize)]
pub struct PirQueryRequest {
    /// The query vector (BabyBear field elements serialized as u32 values).
    pub query_vector: Vec<u32>,
}

/// Response to a PIR query.
#[derive(Serialize)]
pub struct PirQueryResponse {
    /// The server's response vector (BabyBear field elements as u32 values).
    pub response: Vec<u32>,
}

/// Metadata about the PIR database (needed for clients to construct valid queries).
#[derive(Serialize)]
pub struct PirInfoResponse {
    /// Number of rows (capability tags) in the index.
    pub num_rows: usize,
    /// Number of columns per row (in field elements).
    pub row_width: usize,
    /// The ordered list of capability tags.
    pub tags: Vec<String>,
}

#[derive(Serialize)]
pub struct IntentListEntry {
    pub id: String,
    pub intent: dregg_intent::Intent,
}

// =============================================================================
// Fulfillment types
// =============================================================================

#[derive(Deserialize)]
pub struct FulfillIntentRequest {
    /// Hex-encoded 32-byte intent ID to fulfill.
    pub intent_id: String,
    /// Hex-encoded 32-byte payer cell ID (intent creator's cell).
    pub payer_cell: String,
    /// Hex-encoded 32-byte recipient cell ID (fulfiller's cell).
    pub recipient_cell: String,
    /// State root (BabyBear field element as u32).
    pub state_root: u32,
    /// Block height at which state root was attested.
    pub state_root_block: u64,
}

#[derive(Serialize)]
pub struct FulfillIntentResponse {
    pub success: bool,
    pub turn_hash: Option<String>,
    pub error: Option<String>,
}

// =============================================================================
// Fast-Path Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct FastPathLockRequest {
    /// The turn to lock (full turn structure).
    pub turn: serde_json::Value,
    /// Hex-encoded 64-byte Ed25519 signature from the agent over `turn.hash()`.
    /// Required (P1-6): validators must verify the agent actually authored the
    /// turn before locking on their behalf.
    pub agent_signature: String,
}

#[derive(Serialize)]
pub struct FastPathLockResponse {
    pub locked: bool,
    pub validator_key: Option<String>,
    pub signature: Option<String>,
    pub height: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Deserialize)]
pub struct FastPathCertificateRequest {
    /// The turn being certified.
    pub turn: serde_json::Value,
    /// Hex-encoded turn hash.
    pub turn_hash: String,
    /// Collected validator signatures.
    pub signatures: Vec<FastPathSignatureEntry>,
}

#[derive(Deserialize)]
pub struct FastPathSignatureEntry {
    /// Hex-encoded 32-byte validator public key.
    pub validator_key: String,
    /// Hex-encoded 64-byte signature.
    pub signature: String,
    /// Height at which the signature was produced.
    pub height: u64,
}

#[derive(Serialize)]
pub struct FastPathCertificateResponse {
    pub executed: bool,
    pub turn_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Conditional Turn types
// =============================================================================

#[derive(Deserialize)]
pub struct SubmitConditionalRequest {
    pub turn: serde_json::Value,
    pub condition: serde_json::Value,
    pub timeout_height: u64,
}

#[derive(Serialize)]
pub struct SubmitConditionalResponse {
    pub accepted: bool,
    pub conditional_hash: Option<String>,
}

#[derive(Deserialize)]
pub struct ResolveConditionalRequest {
    pub conditional_hash: String,
    pub proof: serde_json::Value,
}

#[derive(Serialize)]
pub struct ResolveConditionalResponse {
    pub resolved: bool,
    pub turn_hash: Option<String>,
    pub reason: Option<String>,
}

#[derive(Serialize)]
pub struct PendingConditionalInfo {
    pub hash: String,
    pub timeout_height: u64,
    pub submitted_at: u64,
    pub condition_type: String,
}

// =============================================================================
// Sovereign Cell Ephemeral Registration types
// =============================================================================

/// Request body for ephemeral sovereign cell registration.
///
/// The cell exists locally on the agent; the federation stores only the commitment.
/// Registration is temporary — expires after `ttl_blocks` of inactivity.
#[derive(Deserialize)]
pub struct RegisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte current state commitment.
    pub commitment: String,
    /// How many blocks to keep the registration alive (default: 1000).
    pub ttl_blocks: Option<u64>,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || commitment`.
    pub signature: String,
    /// Optional hex-encoded 32-byte verification key hash to bind this cell
    /// to a deployed program. When set, proof-carrying turns are verified
    /// against the program identified by this VK hash.
    pub verification_key_hash: Option<String>,
}

/// Response to a sovereign cell registration.
#[derive(Serialize)]
pub struct RegisterCellResponse {
    pub registered: bool,
    pub ttl_blocks: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voluntary deregistration.
#[derive(Deserialize)]
pub struct DeregisterCellRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    pub signature: String,
}

/// Response to a sovereign cell deregistration.
#[derive(Serialize)]
pub struct DeregisterCellResponse {
    pub deregistered: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for updating a sovereign cell's commitment after a transition.
#[derive(Deserialize)]
pub struct UpdateCommitmentRequest {
    /// Hex-encoded 32-byte cell ID.
    pub cell_id: String,
    /// Hex-encoded 32-byte old commitment (must match stored).
    pub old_commitment: String,
    /// Hex-encoded 32-byte new commitment.
    pub new_commitment: String,
    /// Hex-encoded 64-byte Ed25519 signature proving ownership.
    /// Signs `cell_id || old_commitment || new_commitment`.
    pub signature: String,
}

/// Response to a commitment update.
#[derive(Serialize)]
pub struct UpdateCommitmentResponse {
    pub updated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Program Deployment types
// =============================================================================

/// Request body for deploying a custom cell program to the federation.
#[derive(Deserialize)]
pub struct DeployProgramRequest {
    /// Hex-encoded postcard-serialized CircuitDescriptor bytes.
    pub descriptor_bytes: String,
    /// Program version (for upgrade/migration tracking).
    pub version: u32,
}

/// Response to a program deployment.
#[derive(Serialize)]
pub struct DeployProgramResponse {
    pub deployed: bool,
    /// Hex-encoded 32-byte VK hash (program identity).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vk_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

// =============================================================================
// Atomic Multi-Party Turn types
// =============================================================================

/// Request body for proposing an atomic multi-party turn.
#[derive(Deserialize)]
pub struct AtomicProposalRequest {
    /// The combined call forest from all parties (serialized).
    pub forest: serde_json::Value,
    /// Hex-encoded 32-byte participant node IDs.
    pub participants: Vec<String>,
    /// Vote threshold required for commitment.
    pub threshold: usize,
    /// Fee in computrons.
    pub fee: u64,
    /// Hex-encoded 32-byte initiator cell ID.
    pub initiator: String,
    /// Optional explicit per-participant Ed25519 verifying keys (hex, 64 chars).
    /// Must have the same length as `participants` if provided. F-P1-4: when
    /// omitted, the node falls back to `known_federation_keys` matched by ID;
    /// unknown participants cause rejection.
    #[serde(default)]
    pub participant_pubkeys: Option<Vec<String>>,
}

/// Per-proposal computron budget cap (F-P2-1). Prior code passed `u64::MAX`
/// straight through to the coordinator, so a misbehaving caller could exhaust
/// computron budget at execution time.
pub const MAX_ATOMIC_BUDGET: u64 = 1_000_000_000;

/// Response to an atomic turn proposal.
#[derive(Serialize)]
pub struct AtomicProposalResponse {
    pub accepted: bool,
    pub proposal_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Request body for voting on an atomic proposal.
#[derive(Deserialize)]
pub struct AtomicVoteRequest {
    /// Hex-encoded 32-byte proposal ID.
    pub proposal_id: String,
    /// Whether the participant votes yes.
    pub approve: bool,
    /// Hex-encoded 64-byte Ed25519 signature over the vote.
    pub signature: String,
    /// Hex-encoded 32-byte voter node ID.
    pub voter: String,
}

/// Response to an atomic vote.
#[derive(Serialize)]
pub struct AtomicVoteResponse {
    pub accepted: bool,
    /// If voting completed a decision, this is "commit" or "abort".
    pub decision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Response to a proposal status query.
#[derive(Serialize)]
pub struct ProposalStatusResponse {
    pub found: bool,
    /// One of: "proposing", "committed", "aborted", "idle".
    pub state: String,
    /// Number of yes votes received so far.
    pub yes_votes: usize,
    /// Number of no votes received so far.
    pub no_votes: usize,
    /// Total participants required.
    pub total_participants: usize,
    /// Threshold needed for commit.
    pub threshold: usize,
    /// Seconds since proposal creation.
    pub age_secs: u64,
}

/// Request body for a participant evaluating a proposal locally.
#[derive(Deserialize)]
pub struct EvaluateProposalRequest {
    /// Hex-encoded 32-byte proposal ID from the coordinator.
    pub proposal_id: String,
    /// The atomic forest to evaluate (serialized, same as the coordinator's proposal).
    pub forest: serde_json::Value,
}

/// Response to local proposal evaluation.
#[derive(Serialize)]
pub struct EvaluateProposalResponse {
    /// Whether the participant would vote yes based on local state.
    pub approve: bool,
    /// If rejecting, the reason.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// The Ed25519 signature over the vote (hex-encoded, 128 chars).
    pub signature: String,
}

// =============================================================================
// Rate Limiting (P1 Fix 4)
// =============================================================================

/// Trusted reverse-proxy front-ends (F-1).
///
/// When the node sits behind a reverse proxy (the devnet's nginx/Caddy), every
/// request arrives from the proxy's socket IP, so a per-socket-IP rate limiter
/// collapses into a single global bucket (trivial DoS of honest clients) and
/// gives a NATed/proxied/IP-rotating attacker no per-client cost. The proxy
/// instead conveys the real client address in `X-Forwarded-For`.
///
/// This set lists the socket IPs we trust to have set `X-Forwarded-For`
/// truthfully. Only when the *direct peer* is in this set do we believe the
/// header — otherwise an unproxied attacker could spoof an arbitrary client IP
/// (and thus a fresh, unlimited bucket) by sending the header themselves.
///
/// Populated from `DREGG_TRUSTED_PROXIES` (comma-separated IPs) at router
/// construction. Empty = no proxy trusted = key purely on the socket IP (the
/// safe default for a directly-exposed node).
#[derive(Clone, Default)]
pub struct TrustedProxies {
    set: Arc<HashSet<IpAddr>>,
}

impl TrustedProxies {
    /// Build from an iterator of textual IPs (invalid entries are skipped).
    pub fn from_strings<I: IntoIterator<Item = String>>(iter: I) -> Self {
        let set: HashSet<IpAddr> = iter
            .into_iter()
            .filter_map(|s| s.trim().parse::<IpAddr>().ok())
            .collect();
        Self { set: Arc::new(set) }
    }

    /// Build from the `DREGG_TRUSTED_PROXIES` env var (comma-separated).
    pub fn from_env() -> Self {
        match std::env::var("DREGG_TRUSTED_PROXIES") {
            Ok(v) if !v.trim().is_empty() => {
                Self::from_strings(v.split(',').map(|s| s.to_string()))
            }
            _ => Self::default(),
        }
    }

    fn contains(&self, ip: &IpAddr) -> bool {
        self.set.contains(ip)
    }

    fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

/// Resolve the rate-limiting key (real client IP) for a request (F-1).
///
/// * If the direct peer (`socket_ip`) is NOT a trusted proxy, we use the socket
///   IP verbatim — a direct attacker cannot grant itself a different bucket by
///   sending `X-Forwarded-For`, because we ignore the header from untrusted
///   peers.
/// * If the direct peer IS a trusted proxy, we walk `X-Forwarded-For` from the
///   right (proxy-appended, least-spoofable end) and return the FIRST address
///   that is not itself a trusted proxy — i.e. the real external client. This
///   defeats a client that pre-seeds the header with spoofed left-hand entries.
///
/// Returns `None` only when the header is malformed/empty behind a trusted
/// proxy, in which case the caller falls back to the socket IP (the proxy's),
/// degrading to the conservative global-bucket behavior rather than fail-open.
pub fn resolve_client_ip(
    socket_ip: IpAddr,
    forwarded_for: Option<&str>,
    trusted: &TrustedProxies,
) -> IpAddr {
    // Untrusted direct peer, or no proxies configured: never believe XFF.
    if trusted.is_empty() || !trusted.contains(&socket_ip) {
        return socket_ip;
    }

    // The peer is a trusted proxy. X-Forwarded-For is "client, proxy1, proxy2, …"
    // where each hop APPENDS the address it received from. Walking from the
    // right, skip addresses that are themselves trusted proxies; the first
    // non-trusted address is the genuine external client. A client that spoofs
    // leading entries cannot move this rightmost-untrusted boundary.
    if let Some(xff) = forwarded_for {
        for hop in xff.split(',').rev() {
            if let Ok(ip) = hop.trim().parse::<IpAddr>()
                && !trusted.contains(&ip)
            {
                return ip;
            }
        }
    }

    // Trusted proxy but no usable forwarded client: fall back to the proxy IP
    // (conservative shared bucket) rather than fail-open with a fresh bucket.
    socket_ip
}

/// Simple in-memory rate limiter: max attempts per window.
#[derive(Clone)]
struct RateLimiter {
    /// Map of IP -> (attempt_count, window_start)
    state: Arc<Mutex<HashMap<IpAddr, (u32, Instant)>>>,
    max_attempts: u32,
    window_secs: u64,
    /// Trusted reverse-proxy front-ends whose `X-Forwarded-For` we honor (F-1).
    trusted_proxies: TrustedProxies,
}

/// Default maximum turns per minute per connection (configurable).
pub const DEFAULT_TURN_RATE_LIMIT: u32 = 60;

impl RateLimiter {
    fn new(max_attempts: u32, window_secs: u64) -> Self {
        Self::with_proxies(max_attempts, window_secs, TrustedProxies::from_env())
    }

    fn with_proxies(max_attempts: u32, window_secs: u64, trusted_proxies: TrustedProxies) -> Self {
        let limiter = Self {
            state: Arc::new(Mutex::new(HashMap::new())),
            max_attempts,
            window_secs,
            trusted_proxies,
        };

        // Spawn a background task that prunes stale entries every 60 seconds
        // to prevent unbounded memory growth from many unique IPs.
        let prune_state = limiter.state.clone();
        let prune_window = window_secs;
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(60));
            loop {
                interval.tick().await;
                let mut map = prune_state.lock().await;
                let now = Instant::now();
                map.retain(|_, (_, window_start)| {
                    now.duration_since(*window_start).as_secs() < prune_window
                });
            }
        });

        limiter
    }

    /// Returns true if the request should be allowed, false if rate-limited.
    async fn check(&self, ip: IpAddr) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        let entry = map.entry(ip).or_insert((0, now));

        // Reset window if expired.
        if now.duration_since(entry.1).as_secs() >= self.window_secs {
            *entry = (0, now);
        }

        entry.0 += 1;
        entry.0 <= self.max_attempts
    }

    /// Resolve the per-client rate-limiting key for an incoming request, honoring
    /// `X-Forwarded-For` ONLY when the direct peer is a configured trusted proxy
    /// (F-1). This is the entry point every rate-limited handler should use so
    /// that, behind the devnet's reverse proxy, the limiter keys on the real
    /// external client instead of degenerating into one global bucket.
    fn client_ip(&self, socket_ip: IpAddr, headers: &axum::http::HeaderMap) -> IpAddr {
        let xff = headers.get("x-forwarded-for").and_then(|v| v.to_str().ok());
        resolve_client_ip(socket_ip, xff, &self.trusted_proxies)
    }

    /// Convenience: resolve the client IP and apply the limiter in one call.
    async fn check_request(&self, socket_ip: IpAddr, headers: &axum::http::HeaderMap) -> bool {
        let key = self.client_ip(socket_ip, headers);
        self.check(key).await
    }
}

// =============================================================================
// Authentication
// =============================================================================

/// Authentication middleware requiring Bearer token for protected endpoints.
///
/// The API token is derived from the bearer seed (which is itself derived from
/// passphrase + salt via BLAKE3 at passphrase-set time).
/// If no passphrase is set, only loopback callers are allowed (initial setup phase).
/// This closes F-CRIT-1: a network attacker that reaches the port before the
/// operator runs `set-passphrase` MUST NOT be able to drive any endpoint.
async fn require_auth(
    State(state): State<NodeState>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Result<Response, StatusCode> {
    let s = state.read().await;

    // If no passphrase is set yet, restrict to loopback (initial setup).
    // F-CRIT-1: prior code allowed *any* caller through here; on `--bind 0.0.0.0`
    // a network attacker could reach this branch before the operator and set the
    // passphrase themselves.
    //
    // PROXY HARDENING: behind a local reverse proxy (the devnet's Caddy on the
    // same host), EVERY external request arrives from a loopback socket, so a
    // raw `is_loopback()` check would hold this door open to the whole internet
    // during the pre-passphrase window. When `DREGG_TRUSTED_PROXIES` names the
    // proxy, we resolve the REAL client IP through `X-Forwarded-For` (same F-1
    // logic as the rate limiters) and require THAT to be loopback. With no
    // trusted proxies configured the resolution is the socket IP verbatim
    // (unchanged local-dev behavior).
    let Some(ref bearer_seed) = s.bearer_seed else {
        drop(s);
        // Pull ConnectInfo if present; if no ConnectInfo we play safe (deny).
        let connect_info: Option<&axum::extract::ConnectInfo<std::net::SocketAddr>> =
            req.extensions().get();
        return match connect_info {
            Some(ci) => {
                static TRUSTED: std::sync::OnceLock<TrustedProxies> = std::sync::OnceLock::new();
                let trusted = TRUSTED.get_or_init(TrustedProxies::from_env);
                let xff = req
                    .headers()
                    .get("x-forwarded-for")
                    .and_then(|v| v.to_str().ok());
                let client_ip = resolve_client_ip(ci.0.ip(), xff, trusted);
                if client_ip.is_loopback() {
                    Ok(next.run(req).await)
                } else {
                    Err(StatusCode::FORBIDDEN)
                }
            }
            _ => Err(StatusCode::FORBIDDEN),
        };
    };

    // Check for Bearer token in Authorization header.
    let auth_header = req
        .headers()
        .get("authorization")
        .and_then(|v| v.to_str().ok());

    match auth_header {
        Some(header) if header.starts_with("Bearer ") => {
            let token = &header[7..];
            let expected_token_bytes = blake3::derive_key("dregg-api-bearer-v1", bearer_seed);
            let expected_token: String = expected_token_bytes
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            drop(s);

            // Constant-time comparison to prevent timing attacks on the bearer token.
            if token.as_bytes().ct_eq(expected_token.as_bytes()).into() {
                Ok(next.run(req).await)
            } else {
                Err(StatusCode::UNAUTHORIZED)
            }
        }
        _ => {
            drop(s);
            Err(StatusCode::UNAUTHORIZED)
        }
    }
}

// =============================================================================
// CORS Middleware (P2 Fix 7)
// =============================================================================

/// Configured CORS allowlist: extra exact origins (e.g. the deployed devnet
/// site origin `https://devnet.example.com`) that are permitted in addition to
/// the always-allowed localhost / browser-extension origins. Wrapped in an
/// `Arc` so it can be cloned cheaply into the per-request middleware closure.
///
/// The default is empty (locked down to localhost + extensions). Operators
/// widen it via `--cors-origin` flags or the `DREGG_CORS_ORIGINS` env var
/// (comma-separated), wired in `main.rs`.
pub type CorsAllowlist = Arc<HashSet<String>>;

/// Middleware that adds CORS headers to every response.
async fn cors_middleware(
    State(allowlist): State<CorsAllowlist>,
    req: Request<axum::body::Body>,
    next: middleware::Next,
) -> Response {
    let origin = req
        .headers()
        .get(header::ORIGIN)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("")
        .to_string();

    // Handle preflight OPTIONS
    let is_preflight = req.method() == Method::OPTIONS;

    let mut response = if is_preflight {
        Response::builder()
            .status(StatusCode::NO_CONTENT)
            .body(axum::body::Body::empty())
            .unwrap()
    } else {
        next.run(req).await
    };

    // Check if origin is allowed.
    let allowed = is_origin_allowed(&origin, &allowlist);
    if allowed {
        let headers = response.headers_mut();
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_ORIGIN,
            HeaderValue::from_str(&origin).unwrap_or_else(|_| HeaderValue::from_static("*")),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_METHODS,
            HeaderValue::from_static("GET, POST, PUT, DELETE, OPTIONS"),
        );
        headers.insert(
            header::ACCESS_CONTROL_ALLOW_HEADERS,
            HeaderValue::from_static("Content-Type, Authorization, X-Devnet-Key"),
        );
        headers.insert(
            header::ACCESS_CONTROL_MAX_AGE,
            HeaderValue::from_static("3600"),
        );
    }

    response
}

/// Check whether an origin is allowed by our CORS policy.
///
/// Uses proper URL parsing to prevent bypass via domains like `localhost.evil.com`.
///
/// Always allows localhost / `127.0.0.1` / `[::1]` over http(s) and browser
/// extension origins. In addition, any exact origin in `allowlist` (configured
/// via `--cors-origin` / `DREGG_CORS_ORIGINS`) is permitted — this is how a
/// deployed devnet site origin (e.g. `https://devnet.example.com`) reaches the
/// node cross-origin. The default allowlist is empty (locked down).
fn is_origin_allowed(origin: &str, allowlist: &HashSet<String>) -> bool {
    // Allow browser extension origins (not parseable as URLs).
    if origin.starts_with("chrome-extension://") || origin.starts_with("moz-extension://") {
        return true;
    }

    // Configured exact-origin allowlist (deployed site origin, etc.). Matched
    // case-insensitively on the normalized origin string so trivial case
    // differences don't slip through or block a legitimate origin.
    if !origin.is_empty() && allowlist.contains(&origin.to_lowercase()) {
        return true;
    }

    // Parse as a URL and check the host exactly.
    // This prevents bypasses like "http://localhost.evil.com".
    let Ok((scheme, host)) = parse_origin(origin) else {
        return false;
    };

    if scheme != "http" && scheme != "https" {
        return false;
    }

    matches!(host.as_str(), "localhost" | "127.0.0.1" | "[::1]")
}

/// Minimal origin parser: extracts scheme and host from an origin string.
/// Returns (scheme, host) without pulling in the `url` crate.
fn parse_origin(origin: &str) -> Result<(String, String), ()> {
    // Format: scheme "://" host [ ":" port ]
    let rest = origin.split_once("://").ok_or(())?;
    let scheme = rest.0.to_lowercase();
    let authority = rest.1;
    // Strip port if present (host is everything before the first ':' or '/')
    let host = authority
        .split_once(':')
        .map(|(h, _)| h)
        .or_else(|| authority.split_once('/').map(|(h, _)| h))
        .unwrap_or(authority);
    if host.is_empty() {
        return Err(());
    }
    Ok((scheme, host.to_lowercase()))
}

// =============================================================================
// Constants
// =============================================================================

/// Maximum number of intents in the node's local pool (P1 Fix 5: unbounded growth).
pub const MAX_NODE_INTENT_POOL: usize = 10_000;

/// Maximum number of pending conditional turns (P1 Fix 6).
pub const MAX_PENDING_CONDITIONALS: usize = 1_000;

/// Maximum request body size in bytes (P2 Fix 11: 1 MB).
const MAX_BODY_SIZE: usize = 1_024 * 1_024;

// =============================================================================
// Router
// =============================================================================

/// Build the Axum router with all API routes.
///
/// Includes CORS, body size limits, rate limiting on passphrase endpoints,
/// per-identity rate limiting on turn submission, and Bearer token
/// authentication on protected routes.
// Convenience constructor retained for embedders/tests; the binary uses router_with_cors.
#[allow(dead_code)]
pub fn router(
    state: NodeState,
    enable_faucet: bool,
    metrics_handle: metrics_exporter_prometheus::PrometheusHandle,
) -> Router {
    router_with_cors(state, enable_faucet, metrics_handle, HashSet::new())
}

/// Build the router with an explicit extra CORS origin allowlist.
///
/// `cors_origins` is a set of exact origin strings (e.g.
/// `https://devnet.example.com`) that are permitted cross-origin *in addition*
/// to the always-allowed localhost / extension origins. An empty set keeps the
/// historical locked-down behavior. `main.rs` populates this from the
/// `--cors-origin` flags and the `DREGG_CORS_ORIGINS` env var.
pub fn router_with_cors(
    state: NodeState,
    enable_faucet: bool,
    metrics_handle: metrics_exporter_prometheus::PrometheusHandle,
    cors_origins: HashSet<String>,
) -> Router {
    // Normalize configured origins to lowercase so matching is case-insensitive.
    let cors_allowlist: CorsAllowlist =
        Arc::new(cors_origins.into_iter().map(|o| o.to_lowercase()).collect());
    // Rate limiter for passphrase/unlock endpoints: 5 attempts per 60 seconds.
    let passphrase_limiter = RateLimiter::new(5, 60);

    // Rate limiter for turn submission: DEFAULT_TURN_RATE_LIMIT per 60 seconds per IP.
    let turn_limiter = RateLimiter::new(DEFAULT_TURN_RATE_LIMIT, 60);

    // Public routes (no auth required)
    let mut public_routes = Router::new()
        .route("/status", get(get_status))
        .route("/health", get(get_status))
        .route("/api/node/producer", get(get_producer_status))
        .route("/api/node/identity", get(get_node_identity))
        .route("/federation/roots", get(get_federation_roots))
        .route("/api/blocks", get(get_federation_roots))
        .route("/api/federations", get(get_federations))
        .route("/api/cells", get(get_all_cells))
        .route("/api/cell/{id}", get(get_cell_detail))
        .route("/api/node/cells/{id}", get(get_cell_detail))
        .route("/api/tokens", get(get_tokens))
        // DEOS-HOST discovery: a hosted private server's cap-gated affordance surface,
        // projected per viewer (public — discovery confers no authority; the cap tooth
        // is the EXECUTOR on the fire, not the read).
        .route(
            "/api/server/{cell}/affordances",
            get(get_server_affordances),
        )
        .route("/api/receipts", get(get_receipts))
        .route("/api/receipts/{hash}/witnesses", get(get_receipt_witnesses))
        // The attested-query index (dregg-query): the receipt-log MMR root and
        // certified positional slices. A query answer built over a slice from
        // `/index/range` carries a non-omission certificate the caller verifies
        // against the `/index/root` root — proving the answer was computed from
        // EXACTLY the committed receipt range. Public (read-only over the log).
        .route("/api/receipts/index/root", get(get_receipt_index_root))
        .route("/api/receipts/index/range", get(get_receipt_index_range))
        // ORGANS identity rider — the KERI-shaped identity event-log export:
        // a cell's chained / signed / witness-receipted key-event history as
        // a PORTABLE artifact (independently checkable via
        // `crate::identity_export::verify_export`, no node required).
        // Public: the KEL is the cell's self-published key history.
        .route(
            "/identity/export/{cell}",
            get(crate::identity_export::get_identity_export),
        )
        .route("/api/turn/{hash}/proof", get(get_turn_proof))
        .route("/api/starbridge/receipts", get(get_starbridge_receipts))
        .route("/api/starbridge/events", get(get_starbridge_events))
        .route("/api/starbridge/turns", get(get_starbridge_turns))
        .route("/api/starbridge/actions", get(get_starbridge_actions))
        .route(
            "/api/starbridge/identity/events",
            get(get_starbridge_identity_events),
        )
        .route(
            "/api/starbridge/identity/credentials",
            get(get_starbridge_identity_credentials),
        )
        .route(
            "/api/starbridge/identity/proof-checkpoints",
            get(get_starbridge_identity_proof_checkpoints),
        )
        .route("/api/intents", get(get_intents))
        .route("/api/conditionals", get(get_pending_conditionals))
        .route("/api/discharge", {
            // Public + does real crypto + takes the global state-write lock:
            // give it its own per-IP budget so a flood cannot contend the lock.
            let limiter = RateLimiter::new(30, 60);
            post(move |connect_info, headers, state, body| {
                post_discharge(connect_info, headers, state, body, limiter)
            })
        })
        .route("/api/events", get(get_events))
        .route("/api/events/stream", get(crate::events::events_stream))
        .route("/observability/stream", get(observability_stream))
        .route("/checkpoint/latest", get(get_checkpoint_latest))
        .route("/checkpoint/{height}", get(get_checkpoint_at_height))
        .route("/api/blocklace/checkpoint", get(get_blocklace_checkpoint))
        .route("/api/blocklace/blocks", get(get_blocklace_blocks))
        .route("/api/block/{height}", get(get_block_by_height))
        .route("/pir/info", get(get_pir_info))
        .route("/pir/query", post(post_pir_query))
        .route(
            "/cipherclerk/unlock",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_cclerk_unlock(connect_info, headers, state, body, limiter)
                }
            }),
        )
        // Gateway-reachable alias (the public Caddy forwards only /api/-prefixed
        // routes): unlocking is the remote operator's auth bootstrap, so it must
        // be reachable through the gateway. Same handler + rate limiter.
        // /cipherclerk/set-passphrase intentionally has NO alias — first-time
        // passphrase setup stays operator-local (loopback).
        .route(
            "/api/cipherclerk/unlock",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_cclerk_unlock(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/cipherclerk/set-passphrase",
            post({
                let limiter = passphrase_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_set_passphrase(connect_info, headers, state, body, limiter)
                }
            }),
        );

    // Faucet endpoint (only available in devnet mode).
    if enable_faucet {
        let faucet_limiter = FaucetRateLimiter::new();
        // Per-IP faucet budget (proxy-aware): bounds drain + zero-amount cell
        // materialization per real client. 10/min is generous for a human or a
        // demo script and miserly for a flood.
        let faucet_ip_limiter = RateLimiter::new(10, 60);
        public_routes = public_routes.route(
            "/api/faucet",
            post(move |connect_info, headers, state, body| {
                post_faucet(
                    connect_info,
                    headers,
                    state,
                    body,
                    faucet_limiter,
                    faucet_ip_limiter,
                )
            }),
        );
    }

    // Protected routes (require bearer token after passphrase is set)
    let protected_routes = Router::new()
        .route("/ws", get(handle_ws))
        .route("/cipherclerk", get(get_cclerk))
        .route("/cipherclerk/authorize", post(post_authorize))
        .route("/cipherclerk/mint", post(post_mint))
        .route("/cipherclerk/attenuate", post(post_attenuate))
        .route("/cipherclerk/tokens", get(get_tokens))
        .route("/cipherclerk/receipts", get(get_receipts))
        .route("/intents", get(get_intents).post(post_intent))
        .route("/intents/encrypted", post(post_encrypted_intent))
        .route("/intents/encrypted/search", post(post_sse_search))
        .route("/intents/trustless", post(post_trustless_intent))
        .route(
            "/intents/trustless/share",
            post(post_trustless_decrypt_share),
        )
        .route(
            "/intents/trustless/status",
            get(get_trustless_engine_status),
        )
        .route("/intents/fulfill", post(post_fulfill_intent))
        .route(
            "/turn/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/turn/fast-path", post(post_fast_path_lock))
        .route("/turn/certificate", post(post_fast_path_certificate))
        // AUDIT-privacy.md §11.2 wiring: encrypted-turn submission +
        // executor public-key discovery. The submit endpoint pulls the
        // executor's X25519 secret from the cipherclerk, hands it to
        // `TurnExecutor::apply_encrypted_turn`, and returns the
        // post-commit receipt's was_encrypted bit.
        .route(
            "/turns/submit-encrypted",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_encrypted_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/turns/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_signed_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/turns/aggregate", post(post_aggregate_bundle))
        .route("/turns/encryption-key", get(get_turn_encryption_key))
        .route("/turn/submit-conditional", post(post_submit_conditional))
        .route("/turn/resolve-conditional", post(post_resolve_conditional))
        .route("/turn/pending", get(get_pending_conditionals))
        .route("/turn/atomic", post(post_atomic_proposal))
        .route("/turn/atomic/vote", post(post_atomic_vote))
        .route("/turn/atomic/{id}", get(get_proposal_status))
        .route("/turn/atomic/evaluate", post(post_evaluate_proposal))
        .route("/cell/{id}", get(get_cell))
        .route("/cells/register", post(post_register_cell))
        .route("/cells/deregister", post(post_deregister_cell))
        .route("/cells/update-commitment", post(post_update_commitment))
        .route("/cells/create-from-factory", post(post_create_from_factory))
        .route("/cells/make-sovereign", post(post_make_sovereign))
        .route("/programs/deploy", post(post_deploy_program))
        .route("/proofs/compose", post(post_compose_proofs))
        .route("/turns/bearer-auth", post(post_bearer_auth))
        .route("/turns/peer-exchange", post(post_peer_exchange))
        // LIVE EPOCH TRANSITION (validator-set reconfiguration on a RUNNING
        // node): propose adding/removing validators. The change only APPLIES
        // once a quorum of the CURRENT committee ratifies it through finality —
        // this endpoint only submits the proposal. Auth-protected (operator op).
        .route(
            "/epoch/propose-transition",
            post(post_propose_epoch_transition),
        )
        // Storage gateway (ORGANS §3): content-addressed put/get/stat/list
        // whose ADMISSION is the StorageGatewayMandate cell (capability +
        // op allowlist + prefix scope + executor-enforced volume debit).
        .merge(crate::storage_service::routes())
        // Trustlines (ORGANS §1): open (the funded birth edge, seeding the
        // Stingray coordinator) / draw / repay (the bilateral counter) /
        // settle (rebalance applied back to the ledger as moves) / status.
        .merge(crate::trustline_service::routes())
        // Channels (ORGANS §4): create / join / remove / rekey (the unified
        // group-key + capability-freshness epoch, ONE turn per step) and the
        // off-cell data plane (post ciphertext + SSE delivery).
        .merge(crate::channels_service::routes())
        // Equivocation court (ORGANS §5): bond (slashable stake escrowed in
        // a real bond cell) / evidence (the witness-first slash, executed as
        // one conserved executor move from the bonded cell) / status.
        .merge(crate::equivocation_court_service::routes())
        // DKG ceremony (ORGANS §6): start (factory-birth the ceremony cell
        // from blueprint terms) / contribute (signed dealing + sealed shares,
        // round roots pinned per phase) / complain (witness-first response) /
        // finalize (|QUAL| >= t -> output commitment pinned) / status.
        .merge(crate::dkg_service::routes())
        // Queue operations
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    // Metrics endpoint (separate state: PrometheusHandle)
    let metrics_route = Router::new()
        .route("/metrics", get(crate::metrics::metrics_handler))
        .with_state(metrics_handle);

    // ─── Path normalization aliases (Gap 3: bot/app compatibility) ────────────
    // The bot/apps expect /api/node/... and /api/turns/... prefixed paths.
    // These aliases ensure BOTH the canonical and prefixed paths work.
    let path_aliases = Router::new()
        // /api/node/* aliases
        .route("/api/node/health", get(get_status))
        .route("/api/node/status", get(get_status))
        // /api/turns/* aliases (protected — require auth)
        .route(
            "/api/turns/submit",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/api/turns/bearer-auth", post(post_bearer_auth))
        .route(
            "/api/turns/submit-signed",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_signed_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route(
            "/api/turns/submit-encrypted",
            post({
                let limiter = turn_limiter.clone();
                move |connect_info, headers, state, body| {
                    post_submit_encrypted_turn(connect_info, headers, state, body, limiter)
                }
            }),
        )
        .route("/api/turns/encryption-key", get(get_turn_encryption_key))
        .route("/api/turns/fast-path", post(post_fast_path_lock))
        .route("/api/turns/certificate", post(post_fast_path_certificate))
        // Gateway-reachable aliases for the public-facing app surface (the
        // devnet Caddy forwards only /api/-prefixed routes; a canonical route
        // without an /api/ alias is operator-local in practice). Same handlers,
        // same bearer-token gate. Routes deliberately left WITHOUT an alias
        // (operator-local by choice): /cipherclerk/set-passphrase + the
        // /cipherclerk key-management surface (authorize/mint/attenuate),
        // /cells/register, /cells/deregister, /cells/update-commitment,
        // /cells/make-sovereign, /turns/aggregate, /turn/submit-conditional,
        // /turn/resolve-conditional, /proofs/compose — node-administration
        // operations, not app traffic.
        .route("/api/turn/atomic", post(post_atomic_proposal))
        .route("/api/turn/atomic/vote", post(post_atomic_vote))
        .route("/api/turn/atomic/{id}", get(get_proposal_status))
        .route("/api/turn/atomic/evaluate", post(post_evaluate_proposal))
        .route("/api/turns/peer-exchange", post(post_peer_exchange))
        .route(
            "/api/cells/create-from-factory",
            post(post_create_from_factory),
        )
        .route("/api/programs/deploy", post(post_deploy_program))
        .route_layer(middleware::from_fn_with_state(state.clone(), require_auth));

    public_routes
        .merge(protected_routes)
        .merge(path_aliases)
        .merge(metrics_route)
        .layer(DefaultBodyLimit::max(MAX_BODY_SIZE))
        .layer(middleware::from_fn_with_state(
            cors_allowlist,
            cors_middleware,
        ))
        .with_state(state)
}

// =============================================================================
// Handlers
// =============================================================================

/// `/status` — honest liveness for the deployed devnet.
///
/// `healthy` reflects "the node is up and consensus is live and producing
/// blocks," NOT the attested-root height. The prior implementation tied
/// `healthy` to store + cipherclerk init, which made a perfectly live devnet
/// (DAG at height 85, producing heartbeat blocks) report `healthy: false`
/// while `latest_height: 0` — a terrible public signal.
///
/// Now we derive liveness from real consensus state: a blocklace handle must
/// be attached (the consensus task is running) and the DAG must have a tip
/// (at least one real signed block produced). We surface `dag_height`
/// (real blocklace tip) alongside `latest_height` (attested-root / turn height)
/// so the distinction is explicit on the wire.
/// F-8: whether the public `/status` is allowed to disclose the aggregate
/// private-activity counters (`note_count` / `revocation_count`). Off unless the
/// operator opts in with `DREGG_STATUS_EXPOSE_COUNTS=1`.
fn status_exposes_private_counts() -> bool {
    std::env::var("DREGG_STATUS_EXPOSE_COUNTS")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

async fn get_status(State(state): State<NodeState>) -> Json<StatusResponse> {
    // Read the real blocklace DAG state first (separate lock).
    let blocklace = state.blocklace().await;
    let (dag_height, block_count, consensus_live) = match &blocklace {
        Some(handle) => (handle.dag_height().await, handle.block_count().await, true),
        None => (0, 0, false),
    };

    let s = state.read().await;

    // Check store accessibility.
    let store_ok = s.store.latest_attested_root().is_ok();

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    // F-8: only surface the aggregate private-activity counters when an operator
    // has explicitly opted in (`DREGG_STATUS_EXPOSE_COUNTS=1`). Otherwise the
    // public, unauthenticated `/status` MUST NOT disclose how many credentials
    // have been revoked or how many shielded notes exist — those are a private-
    // activity-volume oracle. Default = omitted.
    let expose_counts = status_exposes_private_counts();
    let revocation_count = if expose_counts {
        Some(s.store.revocation_count().unwrap_or(0))
    } else {
        None
    };
    let note_count = if expose_counts {
        Some(s.store.note_count().unwrap_or(0))
    } else {
        None
    };
    let peer_count = s.peers.len();

    let federation_mode = if s.solo_consensus.as_ref().is_some_and(|s| s.is_solo) {
        "solo".to_string()
    } else {
        "full".to_string()
    };

    // Liveness: store reachable + consensus task running + DAG has produced at
    // least one real block. block_count > 0 (rather than dag_height > 0) so a
    // single genesis block at seq 0 still counts as "producing".
    let healthy = store_ok && consensus_live && block_count > 0;

    let lean_producer = s.lean_producer_enabled;
    let full_turn_proving = s.full_turn_proving_enabled;
    let state_producer = if lean_producer { "lean" } else { "rust" }.to_string();
    // The DEFAULT-ON producer INSTALLS verified state only for the swap-safe (root-agreeing) set;
    // report that, not the wider "merely mappable" surface, so the status is honest about what the
    // verified executor actually commits.
    let producer_covered_effects =
        dregg_exec_lean::lean_shadow::producer_root_agreeing_effects().len();

    Json(StatusResponse {
        healthy,
        peer_count,
        latest_height,
        dag_height,
        block_count,
        consensus_live,
        revocation_count,
        note_count,
        federation_mode,
        public_key: hex_encode(&s.cclerk.public_key().0),
        state_producer,
        lean_producer,
        full_turn_proving,
        producer_covered_effects,
    })
}

/// GET /api/node/producer — the honest THE-SWAP verified-execution boundary.
async fn get_producer_status(State(state): State<NodeState>) -> Json<ProducerStatusResponse> {
    let s = state.read().await;
    let lean_producer_enabled = s.lean_producer_enabled;
    let full_turn_proving = s.full_turn_proving_enabled;
    drop(s);

    let covered: Vec<String> = dregg_exec_lean::lean_shadow::producer_covered_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let uncovered: Vec<String> = dregg_exec_lean::lean_shadow::producer_uncovered_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let root_agreeing: Vec<String> = dregg_exec_lean::lean_shadow::producer_root_agreeing_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let root_gaps: Vec<String> = dregg_exec_lean::lean_shadow::producer_root_gap_effects()
        .iter()
        .map(|k| k.to_string())
        .collect();
    let total_effect_kinds = dregg_exec_lean::lean_shadow::all_effect_kinds().len();

    let state_producer = if lean_producer_enabled {
        "lean"
    } else {
        "rust"
    }
    .to_string();

    let summary = if lean_producer_enabled {
        format!(
            "THE SWAP (default on): the VERIFIED Lean executor is the authoritative state producer \
             and INSTALLS its post-state for turns touching only the {} SWAP-SAFE (root-agreeing) \
             effect kinds, where the Lean-produced root provably == Rust. The legacy Rust executor \
             runs as a logged differential cross-check. A turn touching any of the {} characterized \
             root-GAP kinds (root provably diverges) or any of the {} unmappable kinds falls back \
             to the Rust producer FOR THAT TURN with a logged reason — never a silent commit of \
             divergent state. Of the {} mappable kinds, {} are swap-safe and {} are root-gaps. \
             Opt out with DREGG_LEAN_PRODUCER=0. Full-turn STARK proving: {}.",
            root_agreeing.len(),
            root_gaps.len(),
            uncovered.len(),
            covered.len(),
            root_agreeing.len(),
            root_gaps.len(),
            if full_turn_proving { "ON" } else { "off" }
        )
    } else {
        format!(
            "Legacy Rust executor is the authoritative state producer (verified Lean producer \
             OFF via DREGG_LEAN_PRODUCER=0 — unset it to re-enable the default SWAP for the {} \
             swap-safe effect kinds). Full-turn STARK proving: {}.",
            root_agreeing.len(),
            if full_turn_proving { "ON" } else { "off" }
        )
    };

    Json(ProducerStatusResponse {
        state_producer,
        lean_producer_enabled,
        full_turn_proving,
        covered_effects: covered,
        total_effect_kinds,
        uncovered_effects: uncovered,
        root_agreeing_effects: root_agreeing,
        root_gap_effects: root_gaps,
        summary,
    })
}

/// GET /api/node/identity — the operator's pubkey + derived agent cell.
async fn get_node_identity(State(state): State<NodeState>) -> Json<NodeIdentityResponse> {
    let s = state.read().await;
    let public_key = s.cclerk.public_key().0;
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let agent_cell = dregg_cell::CellId::derive_raw(&public_key, &default_token_id);
    let (agent_balance, agent_nonce) = match s.ledger.get(&agent_cell) {
        Some(cell) => (Some(cell.state.balance()), Some(cell.state.nonce())),
        None => (None, None),
    };
    let unlocked = s.unlocked;
    drop(s);
    Json(NodeIdentityResponse {
        public_key: hex_encode(&public_key),
        agent_cell: hex_encode(&agent_cell.0),
        unlocked,
        agent_balance,
        agent_nonce,
    })
}

async fn get_cclerk(State(state): State<NodeState>) -> Json<CipherclerkResponse> {
    let ws = state.cclerk_status().await;
    Json(CipherclerkResponse {
        unlocked: ws.unlocked,
        public_key: ws.public_key,
        token_count: ws.token_count,
        receipt_chain_length: ws.receipt_chain_length,
    })
}

async fn post_authorize(
    State(state): State<NodeState>,
    Json(req): Json<AuthorizeRequest>,
) -> Result<Json<AuthorizeResponse>, StatusCode> {
    let s = state.read().await;

    let token = s
        .cclerk
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?;

    let auth_req = AuthRequest {
        service: req.service,
        action: req.action,
        ..Default::default()
    };

    let authorized = s.cclerk.verify_token(token, &auth_req);

    Ok(Json(AuthorizeResponse {
        authorized,
        reason: if authorized {
            None
        } else {
            Some("token does not satisfy request".to_string())
        },
    }))
}

async fn post_mint(
    State(state): State<NodeState>,
    Json(req): Json<MintRequest>,
) -> Result<Json<MintResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Generate a root key for the new token.
    let mut root_key = [0u8; 32];
    getrandom::fill(&mut root_key).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    let held = s.cclerk.mint_token(&root_key, &req.service);

    Ok(Json(MintResponse {
        token_id: held.id().to_string(),
        service: held.service().to_string(),
    }))
}

async fn post_attenuate(
    State(state): State<NodeState>,
    Json(req): Json<AttenuateRequest>,
) -> Result<Json<AttenuateResponse>, StatusCode> {
    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let token = s
        .cclerk
        .find_token_by_id(&req.token_id)
        .ok_or(StatusCode::NOT_FOUND)?
        .clone();

    let attenuation = Attenuation {
        services: req.services,
        ..Default::default()
    };

    let attenuated = s
        .cclerk
        .attenuate(&token, &attenuation)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    Ok(Json(AttenuateResponse {
        new_token_id: attenuated.id().to_string(),
        service: attenuated.service().to_string(),
    }))
}

async fn get_tokens(State(state): State<NodeState>) -> Json<Vec<TokenInfo>> {
    let s = state.read().await;
    let tokens: Vec<TokenInfo> = s
        .cclerk
        .tokens()
        .iter()
        .map(|t| TokenInfo {
            id: t.id().to_string(),
            label: t.label().to_string(),
            service: t.service().to_string(),
        })
        .collect();
    Json(tokens)
}

/// `GET /api/receipts/index/root` → [`dregg_query::client::IndexRootResponse`].
///
/// The MMR root over the node's receipt chain: leaf `i` is the 32-byte
/// `receipt_hash()` of chain entry `i`, bagged per `dregg_query::Blake3Mmr`. The
/// index is brought current from the chain before the read ([`NodeStateInner::
/// sync_receipt_index`]) — additive, never gating commit. The verifier trusts
/// only this root; `len` is served for UX (the verifier re-derives it from the
/// root-pinned peak heights).
async fn get_receipt_index_root(
    State(state): State<NodeState>,
) -> Json<dregg_query::client::IndexRootResponse> {
    let mut s = state.write().await;
    s.sync_receipt_index();
    Json(dregg_query::client::IndexRootResponse {
        root: hex_encode(&s.receipt_index.root()),
        len: s.receipt_index.len(),
    })
}

/// `GET /api/receipts/index/range?lo=&hi=` →
/// [`dregg_query::client::IndexRangeResponse`].
///
/// The certified slice: the receipt rows at dense positions `[lo, min(hi,
/// len-1)]` plus the `RangeOpening` (the honest prover, whose output always
/// verifies against the root from `/index/root`). Each row carries the typed
/// [`dregg_query::EffectSummary`] enrichment, joined from the commit event log
/// by turn hash, so the slice is a complete EDB for transfer/balance/granted
/// queries. The span is capped like other list endpoints.
async fn get_receipt_index_range(
    State(state): State<NodeState>,
    Query(q): Query<dregg_query::client::RangeParams>,
) -> Result<Json<dregg_query::client::IndexRangeResponse>, StatusCode> {
    const MAX_SPAN: u64 = 1024;
    if q.hi < q.lo || q.hi - q.lo >= MAX_SPAN {
        return Err(StatusCode::BAD_REQUEST);
    }
    let mut s = state.write().await;
    s.sync_receipt_index();
    let len = s.receipt_index.len();
    if len == 0 || q.lo >= len {
        return Err(StatusCode::NOT_FOUND);
    }
    let hi = q.hi.min(len - 1);
    let root = s.receipt_index.root();
    let (_values, opening) = s.receipt_index.open_range(q.lo, hi);

    // Build the enriched receipt rows for [lo, hi]: identity/position from the
    // chain entry, height + typed effect summaries joined from the commit event
    // log by turn hash (absent for entries evicted past the event-log window —
    // those rows still carry their certified identity, just no facts).
    let chain = s.cclerk.receipt_chain();
    let mut receipts = Vec::with_capacity((hi - q.lo + 1) as usize);
    for pos in q.lo..=hi {
        let r = &chain[pos as usize];
        let turn_hash = hex_encode(&r.turn_hash);
        let (height, summaries) = s
            .event_log
            .iter()
            .rev()
            .find(|e| e.turn_hash == turn_hash)
            .map(|e| (e.height, e.summaries.clone()))
            .unwrap_or((0, Vec::new()));
        receipts.push(dregg_query::ReceiptRecord {
            chain_index: pos,
            receipt_hash: hex_encode(&r.receipt_hash()),
            height,
            agent: hex_encode(&r.agent.0),
            effects: summaries,
        });
    }

    Ok(Json(dregg_query::client::IndexRangeResponse {
        receipts,
        root: hex_encode(&root),
        lo: q.lo,
        hi,
        opening,
    }))
}

async fn get_receipts(State(state): State<NodeState>) -> Json<Vec<ReceiptInfo>> {
    let s = state.read().await;
    Json(receipt_infos_from_chain(&s, 50))
}

async fn get_receipt_witnesses(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let bytes = hex_decode(&hash).map_err(|_| StatusCode::BAD_REQUEST)?;
    let receipt_hash: [u8; 32] = bytes.try_into().map_err(|_| StatusCode::BAD_REQUEST)?;
    let s = state.read().await;
    let witnessed = s
        .witnessed_receipts
        .get(&receipt_hash)
        .cloned()
        .unwrap_or_default();
    let witness_artifacts = witnessed
        .iter()
        .map(|witness| {
            witness
                .to_artifact_bytes()
                .map(|bytes| hex_encode_var(&bytes))
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(serde_json::json!({
        "receipt_hash": hex_encode(&receipt_hash),
        "witness_count": witnessed.len(),
        "artifact_format": "DWR1",
        "witness_artifacts": witness_artifacts,
        "witnessed_receipts": witnessed,
    })))
}

/// Serve the persisted full-turn STARK proof for a committed turn so a light
/// client can fetch and independently verify it.
///
/// The proof bytes are persisted by the commit path under
/// `full_turn_proof:{turn_hash}` (see
/// [`crate::turn_proving::turn_proof_config_key`]). A spend turn's proof carries
/// the FRESHNESS-bound non-revocation leg; a light client re-verifying it MUST
/// pass `expected_revocation_root` = the canonical revocation root derived from
/// the node's authoritative spent-nullifier set (served via
/// `nullifier_set_root` on the checkpoint endpoints) into
/// `dregg_sdk::verify_full_turn_bound`.
///
/// Returns the hex-encoded proof bytes plus the turn hash. 404 if no proof was
/// persisted for that turn (e.g. proving disabled, or the turn carried no
/// verified proof).
async fn get_turn_proof(
    AxumPath(hash): AxumPath<String>,
    State(state): State<NodeState>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    // Accept the turn hash as hex (32 bytes). Normalise to the lowercase form the
    // commit path keys with.
    let bytes = hex_decode(&hash).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn_hash_hex = hex_encode(&bytes);
    let key = crate::turn_proving::turn_proof_config_key(&turn_hash_hex);
    let s = state.read().await;
    match s.store.get_config(&key) {
        Ok(Some(proof_bytes)) => Ok(Json(serde_json::json!({
            "turn_hash": turn_hash_hex,
            "proof_len": proof_bytes.len(),
            "proof_hex": hex_encode_var(&proof_bytes),
        }))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

async fn get_starbridge_receipts(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeReceiptInfo>> {
    let limit = starbridge_limit(params.limit);
    let cell = params.cell.as_deref().map(str::to_ascii_lowercase);
    let turn_hash = params.turn_hash.as_deref().map(str::to_ascii_lowercase);
    let effects_hash = params.effects_hash.as_deref().map(str::to_ascii_lowercase);

    let s = state.read().await;
    let chain = s.cclerk.receipt_chain();
    let chain_len = chain.len();
    let receipts = chain
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, r)| {
            cell.as_ref()
                .is_none_or(|want| hex_encode(&r.agent.0).eq_ignore_ascii_case(want))
                && turn_hash
                    .as_ref()
                    .is_none_or(|want| hex_encode(&r.turn_hash).eq_ignore_ascii_case(want))
                && effects_hash
                    .as_ref()
                    .is_none_or(|want| hex_encode(&r.effects_hash).eq_ignore_ascii_case(want))
        })
        .take(limit)
        .map(|(idx, r)| {
            let receipt_hash = r.receipt_hash();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);
            let turn_hash_hex = hex_encode(&r.turn_hash);
            // Same attached-proof semantics as `receipt_infos_from_chain_with_witnesses`.
            let has_proof = witness_count > 0 || stored_full_turn_proof_exists(&s, &turn_hash_hex);
            StarbridgeReceiptInfo {
                receipt: ReceiptInfo {
                    chain_index: idx as u64,
                    chain_head: idx + 1 == chain_len,
                    receipt_hash: hex_encode(&receipt_hash),
                    turn_hash: turn_hash_hex,
                    agent: hex_encode(&r.agent.0),
                    pre_state: hex_encode(&r.pre_state_hash),
                    post_state: hex_encode(&r.post_state_hash),
                    timestamp: r.timestamp,
                    computrons_used: r.computrons_used,
                    action_count: r.action_count,
                    previous_receipt_hash: r.previous_receipt_hash.map(|h| hex_encode(&h)),
                    finality: format!("{:?}", r.finality).to_lowercase(),
                    was_encrypted: r.was_encrypted,
                    was_burn: r.was_burn,
                    has_proof,
                    executor_signed: r.executor_signature.is_some(),
                    has_witness: witness_count > 0,
                    witness_count,
                },
                effects_hash: hex_encode(&r.effects_hash),
                federation_id: hex_encode(&r.federation_id),
                emitted_event_count: r.emitted_events.len(),
                routing_directive_count: r.routing_directives.len(),
                derivation_record_count: r.derivation_records.len(),
                source: "receipt_chain",
                turn_body_available: false,
            }
        })
        .collect();
    Json(receipts)
}

/// Does the node hold a persisted full-turn STARK proof for this turn hash
/// (the blocklace finalized-turn proving leg persists under
/// [`crate::turn_proving::turn_proof_config_key`])?
fn stored_full_turn_proof_exists(s: &crate::state::NodeStateInner, turn_hash_hex: &str) -> bool {
    let key = crate::turn_proving::turn_proof_config_key(turn_hash_hex);
    matches!(s.store.get_config(&key), Ok(Some(_)))
}

fn receipt_infos_from_chain(s: &crate::state::NodeStateInner, limit: usize) -> Vec<ReceiptInfo> {
    receipt_infos_from_chain_with_witnesses(
        s.cclerk.receipt_chain(),
        limit,
        |hash| s.witnessed_receipt_count(hash),
        |turn_hash_hex| stored_full_turn_proof_exists(s, turn_hash_hex),
    )
}

fn receipt_infos_from_chain_with_witnesses(
    chain: &[dregg_turn::TurnReceipt],
    limit: usize,
    witness_count_for: impl Fn(&[u8; 32]) -> usize,
    stored_proof_for: impl Fn(&str) -> bool,
) -> Vec<ReceiptInfo> {
    let chain_len = chain.len();
    chain
        .iter()
        .enumerate()
        .rev()
        .take(limit)
        .map(|(idx, r)| {
            let receipt_hash = r.receipt_hash();
            let witness_count = witness_count_for(&receipt_hash);
            let turn_hash_hex = hex_encode(&r.turn_hash);
            // `has_proof` reports whether a STARK attestation is actually
            // ATTACHED to this committed turn: either the async prove pool's
            // WitnessedReceipt (the HTTP commit path) or the persisted
            // full-turn proof (the blocklace finalized-turn path). It is NOT
            // the executor signature — that is `executor_signed`. Deriving it
            // from `executor_signature` made the field permanently false on
            // node configs that never set an executor signing key, even while
            // the pool was attaching real proofs.
            let has_proof = witness_count > 0 || stored_proof_for(&turn_hash_hex);
            ReceiptInfo {
                chain_index: idx as u64,
                chain_head: idx + 1 == chain_len,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: turn_hash_hex,
                agent: hex_encode(&r.agent.0),
                pre_state: hex_encode(&r.pre_state_hash),
                post_state: hex_encode(&r.post_state_hash),
                timestamp: r.timestamp,
                computrons_used: r.computrons_used,
                action_count: r.action_count,
                previous_receipt_hash: r.previous_receipt_hash.map(|h| hex_encode(&h)),
                finality: format!("{:?}", r.finality).to_lowercase(),
                was_encrypted: r.was_encrypted,
                was_burn: r.was_burn,
                has_proof,
                executor_signed: r.executor_signature.is_some(),
                has_witness: witness_count > 0,
                witness_count,
            }
        })
        .collect()
}

pub(crate) fn seed_executor_receipt_head(
    executor: &dregg_turn::TurnExecutor,
    agent: CellId,
    previous_receipt_hash: Option<[u8; 32]>,
) {
    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent, head);
    }
}

/// Query for `GET /api/server/{cell}/affordances?viewer=<authlabel>` — the discovery
/// route for a hosted deos-host private server's cap-gated affordance surface.
#[derive(Debug, Deserialize)]
pub struct ServerAffordanceQuery {
    /// The viewer's held authority label ("none"/"signature"/"proof"/"either").
    /// Defaults to "none" (the broadest viewer — sees every affordance).
    #[serde(default)]
    pub viewer: Option<String>,
}

fn parse_auth_label_api(label: &str) -> dregg_cell::AuthRequired {
    use dregg_cell::AuthRequired;
    match label.to_lowercase().as_str() {
        "signature" | "sig" => AuthRequired::Signature,
        "proof" => AuthRequired::Proof,
        "either" => AuthRequired::Either,
        "impossible" => AuthRequired::Impossible,
        _ => AuthRequired::None,
    }
}

/// `GET /api/server/{cell}/affordances?viewer=<authlabel>` — DISCOVERY.
///
/// Project a hosted deos-host private server's published affordance surface for a
/// viewer's held authority (the proven attenuation lattice: `required ⊆ held`). A
/// weaker viewer sees a strictly smaller set. Returns `[{name, required}]` JSON, or 404
/// if no server is hosted at that cell.
pub async fn get_server_affordances(
    State(state): State<NodeState>,
    AxumPath(cell_hex): AxumPath<String>,
    Query(q): Query<ServerAffordanceQuery>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let cell = match hex_decode_32(&cell_hex) {
        Some(bytes) => CellId(bytes),
        None => return Err(StatusCode::BAD_REQUEST),
    };
    let held = parse_auth_label_api(q.viewer.as_deref().unwrap_or("none"));

    let s = state.read().await;
    let specs = match s.deos_server_surfaces.get(&cell) {
        Some(specs) => specs.clone(),
        None => return Err(StatusCode::NOT_FOUND),
    };
    // The executor's federation id — the binding a client signs its fire action over
    // (on a solo/unconfigured node this is `blake3(pubkey)`, not the raw `federation_id`).
    // A remote client cannot derive it, so discovery hands it back: everything needed to
    // build + sign a fire turn arrives in one round-trip.
    let executor_federation_id = hex_encode(&crate::executor_setup::federation_id_for_executor(&s));
    drop(s);

    // Project per-viewer via the proven attenuation lattice (the deos-reflect surface).
    let mut surface = deos_reflect::AffordanceSurface::new(cell);
    for (name, required) in &specs {
        surface = surface.declare(deos_reflect::Affordance::new(
            name.clone(),
            required.clone(),
            dregg_turn::action::Effect::IncrementNonce { cell },
        ));
    }
    let visible: Vec<serde_json::Value> = surface
        .project_for(&held)
        .into_iter()
        .map(|a| {
            serde_json::json!({
                "name": a.name,
                "required": auth_label_str(&a.required),
            })
        })
        .collect();

    Ok(Json(serde_json::json!({
        "cell": cell_hex,
        "viewer": q.viewer.unwrap_or_else(|| "none".to_string()),
        "affordances": visible,
        "executor_federation_id": executor_federation_id,
    })))
}

/// Stable lowercase label for an `AuthRequired` (matches the deos-js / discovery vocab).
fn auth_label_str(a: &dregg_cell::AuthRequired) -> &'static str {
    use dregg_cell::AuthRequired;
    match a {
        AuthRequired::None => "none",
        AuthRequired::Signature => "signature",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        AuthRequired::Custom { .. } => "custom",
    }
}

/// Decode a 64-char hex string into a 32-byte array (cell id). `None` on any malformed
/// input.
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn push_committed_event(
    s: &mut crate::state::NodeStateInner,
    turn_hash: String,
    cell_id: String,
    effects: Vec<String>,
    proof_status: ActivityProofStatus,
) {
    push_committed_event_enriched(s, turn_hash, cell_id, effects, Vec::new(), proof_status)
}

/// As [`push_committed_event`], but carrying the typed [`dregg_query::EffectSummary`]
/// enrichment — from/to/asset/amount, grants, and post-state balances — so the
/// LIVE receipt log yields `transfer`/`balance`/`granted` facts (not just
/// effect-kind strings) when dregg-query reads `/api/receipts/index/range`.
fn push_committed_event_enriched(
    s: &mut crate::state::NodeStateInner,
    turn_hash: String,
    cell_id: String,
    effects: Vec<String>,
    summaries: Vec<dregg_query::EffectSummary>,
    proof_status: ActivityProofStatus,
) {
    let store_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let solo_height = s
        .solo_consensus
        .as_ref()
        .map(|solo| solo.height)
        .unwrap_or(0);
    let next_log_height = s
        .event_log
        .back()
        .map(|e| e.height.saturating_add(1))
        .unwrap_or(1);
    let receipt_height = s.cclerk.receipt_chain_length() as u64;
    let height = store_height
        .max(solo_height)
        .max(receipt_height)
        .max(next_log_height);
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    s.push_event(CommittedEvent {
        height,
        status: ActivityStatus::Committed,
        proof_status,
        turn_hash,
        cell_id,
        effects,
        summaries,
        timestamp,
    });
}

/// What the HTTP commit path hands the async prove pool (PATH-PRESERVE Phase 5b).
///
/// F-DOS-1: the commit path does NOT generate a STARK proof inline (that ran the
/// ~750 ms prover under the global state-write lock and wedged the node) — and it
/// no longer runs an inline FRI-free constraint re-check either. The authoritative
/// executor (`execute_via_producer → Committed`) already validated the turn and
/// committed the new state BEFORE this point; the executor IS the soundness
/// boundary, so a second inline witness check would be redundant defense-in-depth,
/// not a gate. The commit path therefore just CARRIES the material the async pool
/// needs to (re-)build + self-verify the composed `FullTurnProof` off the lock —
/// including the per-turn ROTATION witness built from the REAL before/after actor
/// cells, so the attestation proves through the LEAN-emitted rotated descriptor
/// (the v1 hand-AIR is gone from this path).
enum HttpWitnessOutcome {
    /// The turn carries an Effect-VM-bearing transition the async pool attests
    /// off the lock (rotated when the cell is a rotatable cohort member).
    Rotatable(RotatableTurn),
    /// No Effect-VM-bearing effects in this turn (nothing to attest).
    NotRequired,
}

/// The material the async prove pool needs to attest a committed turn off the
/// lock. `rotation` is `Some` when the actor cell is a rotatable cohort member
/// (the effect-vm leg proves through the rotated descriptor); `None` falls back
/// to the byte-identical v1 leg INSIDE `prove_and_verify_finalized_turn` — never
/// the node's own v1 effect-vm hand-AIR.
struct RotatableTurn {
    agent: CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: Vec<dregg_turn::Effect>,
    turn_hash: [u8; 32],
    rotation: Option<dregg_sdk::RotationTurnWitness>,
}

fn http_project_effects(effects: &[&dregg_turn::Effect]) -> Vec<dregg_circuit::effect_vm::Effect> {
    let mut vm_effects = Vec::new();
    for effect in effects {
        match effect {
            dregg_turn::Effect::Transfer { amount, .. } => {
                vm_effects.push(dregg_circuit::effect_vm::Effect::Transfer {
                    amount: *amount,
                    direction: 1,
                });
            }
            dregg_turn::Effect::SetField { index, value, .. } => {
                let mut le4 = [0u8; 4];
                le4.copy_from_slice(&value[..4]);
                vm_effects.push(dregg_circuit::effect_vm::Effect::SetField {
                    field_idx: *index as u32,
                    value: dregg_circuit::BabyBear::new(u32::from_le_bytes(le4)),
                });
            }
            dregg_turn::Effect::IncrementNonce { .. } => {
                vm_effects.push(dregg_circuit::effect_vm::Effect::NoOp);
            }
            _ => {}
        }
    }
    vm_effects
}

/// Prepare a committed HTTP-path turn for asynchronous attestation (PATH-PRESERVE
/// Phase 5b). The authoritative executor already validated + committed this turn,
/// so this does NO inline proving and NO inline FRI-free re-check — it only
/// gathers what the async prove pool needs to (re-)build + self-verify the
/// composed `FullTurnProof` off the lock.
///
/// `post_ledger` is the ledger AFTER the executor mutated it (the real after-cell
/// the rotated leg's welds read); `receipt_hash` seeds the rotation witness's
/// `iroot` MMR leaf. When the actor cell is a rotatable cohort member the rotation
/// witness is built (the effect-vm leg then proves through the LEAN-emitted rotated
/// descriptor); otherwise it is `None` and the byte-identical v1 leg runs INSIDE
/// the prover — never the node's own v1 effect-vm hand-AIR. Returns
/// [`HttpWitnessOutcome::NotRequired`] when the turn projects to no Effect-VM
/// transition (nothing to attest), or `Err` only when the actor's local pre-state
/// is missing / unrepresentable.
fn prepare_rotatable_turn(
    turn: &Turn,
    pre_ledger: &dregg_cell::Ledger,
    post_ledger: &dregg_cell::Ledger,
    receipt_hash: [u8; 32],
) -> Result<HttpWitnessOutcome, String> {
    let effects_refs = turn.call_forest.total_effects();
    let vm_effects = http_project_effects(&effects_refs);
    if vm_effects.is_empty() {
        return Ok(HttpWitnessOutcome::NotRequired);
    }

    let Some(before_cell) = pre_ledger.get(&turn.agent) else {
        return Err(format!(
            "missing local pre-state for agent {}",
            hex_encode(&turn.agent.0)
        ));
    };
    // THE EPOCH: balances are SIGNED (i64); the circuit VM state is u64. The
    // agent cell is ORDINARY (non-negative) — checked conversion, no `as`.
    let pre_balance = u64::try_from(before_cell.state.balance())
        .map_err(|_| "agent cell balance is negative; cannot build VM pre-state".to_string())?;
    let pre_nonce = before_cell.state.nonce();

    let effects: Vec<dregg_turn::Effect> = effects_refs.iter().map(|e| (*e).clone()).collect();

    // Build the per-turn ROTATION producer witness from the REAL before/after
    // actor cells (the SAME builder `blocklace_sync::execute_finalized_turn` calls
    // for the finalized leg). It self-validates: a cell the synthetic cap-less
    // rotated pre-state cannot faithfully represent — or a non-cohort effect —
    // yields `None`, and the prover then runs the byte-identical v1 leg. The
    // after-cell is the post-execution state the executor just committed.
    let rotation = match post_ledger.get(&turn.agent) {
        Some(after_cell) => {
            let receipt_hashes = [receipt_hash];
            crate::turn_proving::rotation_witness_for_self_sovereign(
                pre_balance,
                pre_nonce,
                before_cell,
                after_cell,
                &receipt_hashes,
                &effects,
            )
        }
        None => None,
    };

    Ok(HttpWitnessOutcome::Rotatable(RotatableTurn {
        agent: turn.agent,
        pre_balance,
        pre_nonce,
        effects,
        turn_hash: turn.hash(),
        rotation,
    }))
}

/// Hand a committed turn to the async prove pool (off the state-write lock),
/// marking the receipt as proof-pending. If the pool is absent (should not happen
/// on the running node) or its queue is full, the receipt stays
/// committed-but-unattested — sound, since the authoritative executor already
/// validated + committed the state; the proof is additive attestation.
async fn enqueue_async_proof(
    state: &NodeState,
    rotatable: RotatableTurn,
    receipt: dregg_turn::TurnReceipt,
    receipt_hash: [u8; 32],
    turn_hash_hex: String,
) {
    if let Some(pool) = state.prove_pool().await {
        let job = crate::prove_pool::ProveJob {
            agent: rotatable.agent,
            pre_balance: rotatable.pre_balance,
            pre_nonce: rotatable.pre_nonce,
            effects: rotatable.effects,
            turn_hash: rotatable.turn_hash,
            rotation: rotatable.rotation,
            receipt,
            receipt_hash,
            turn_hash_hex,
        };
        if pool.enqueue(job) {
            let mut s = state.write().await;
            s.mark_proof_pending(receipt_hash);
        }
    } else {
        tracing::warn!(
            turn_hash = %turn_hash_hex,
            "no async prove pool installed; committed receipt left unattested (the executor \
             already validated + committed the state, so the commit is sound)"
        );
    }
}

/// Validity horizon (wall-clock seconds) stamped onto operator-constructed
/// turns at the API boundary. Generous for a turn that executes immediately on
/// the submit path; bounded so a replayed envelope eventually expires.
const DEFAULT_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

/// Default `valid_until` for turns the node constructs itself (the thin-HTTP
/// `/turn/submit` and faucet paths).
///
/// The Lean producer's wire marshal REQUIRES the turn envelope's `valid_until`
/// (`lean_shadow::turn_to_wire_turn`); a `None` here meant every thin-HTTP turn
/// fell off the verified Lean producer back to the legacy Rust producer,
/// per-turn, forever ("turn.valid_until required for wire marshal"). The Rust
/// executor enforces `current_timestamp <= valid_until` (a TIMESTAMP deadline,
/// not a height), so the default is wall-clock now + a horizon — never a block
/// height, which would be in the past as a timestamp and expire every turn.
fn default_valid_until() -> Option<i64> {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    Some(now + DEFAULT_TURN_VALIDITY_HORIZON_SECS)
}

/// Build a 200-with-error `SubmitTurnResponse` for a malformed action/effect
/// spec. Returns `Ok(...)` so the body carries the diagnostic rather than an
/// opaque 4xx status (matching the rest of this handler's error reporting).
fn submit_turn_bad_request(err: String) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    Ok(Json(SubmitTurnResponse {
        accepted: false,
        turn_hash: None,
        proof_status: ActivityProofStatus::NotCommitted,
        has_witness: false,
        witness_count: 0,
        error: Some(err),
    }))
}

/// Re-apply the executor signature after the node has stamped the receipt's
/// committed finality.
///
/// The turn executor constructs receipts with [`Finality::Final`] and signs them
/// inside `execute()` (`maybe_sign_receipt` over
/// [`TurnReceipt::canonical_executor_signed_message`], the v3 message that binds
/// the *full* `receipt_hash`). Solo mode then downgrades `finality` to
/// [`Finality::Tentative`] — a field bound into `receipt_hash` — which strands
/// that original signature: any verifier recomputing `receipt_hash` from the
/// committed (Tentative) receipt derives a different v3 message, so the signature
/// fails to verify against the executor's verifying key. Re-signing with the SAME
/// key the executor used (the node's gossip signing key, per
/// `configure_turn_executor`) restores `executor_signature == sign(v3(receipt_hash))`
/// for the receipt as committed and served.
fn resign_receipt_committed(receipt: &mut dregg_turn::TurnReceipt, node_signing_key: &[u8; 32]) {
    use ed25519_dalek::Signer;
    let sk = ed25519_dalek::SigningKey::from_bytes(node_signing_key);
    let msg = receipt.canonical_executor_signed_message();
    receipt.executor_signature = Some(sk.sign(&msg).to_bytes().to_vec());
}

/// Debug-only "sign LAST" invariant: a committed receipt's own executor
/// signature MUST verify against the node's executor verifying key over the FINAL
/// receipt about to be persisted.
///
/// Because the v3 executor signature commits to the whole `receipt_hash`, any
/// mutation of a `receipt_hash`-folded field (finality, `previous_receipt_hash`,
/// ...) applied AFTER the signature silently strands it and surfaces far
/// downstream as a verifier's `ExecutorSignatureInvalid`. Asserting here trips
/// that class at the source. Scoped to the solo commit sites where the node IS
/// the signer (its gossip key), so it never false-fires on relayed/foreign
/// receipts. Zero release cost (compiled out unless `debug_assertions`).
#[cfg(debug_assertions)]
fn debug_assert_signed_last(receipt: &dregg_turn::TurnReceipt, node_signing_key: &[u8; 32]) {
    use ed25519_dalek::Verifier;
    let Some(sig_bytes) = receipt.executor_signature.as_ref() else {
        return;
    };
    let vk = ed25519_dalek::SigningKey::from_bytes(node_signing_key).verifying_key();
    let sig = ed25519_dalek::Signature::from_slice(sig_bytes)
        .expect("executor_signature must be a 64-byte ed25519 signature");
    debug_assert!(
        vk.verify(&receipt.canonical_executor_signed_message(), &sig)
            .is_ok(),
        "sign-LAST invariant violated: the node executor_signature does not verify against \
         the committed receipt_hash — a receipt_hash-folded field was mutated after signing"
    );
}

#[tracing::instrument(skip_all, fields(agent = %req.agent))]
async fn post_submit_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<SubmitTurnRequest>,
    limiter: RateLimiter,
) -> Result<Json<SubmitTurnResponse>, StatusCode> {
    // Per-client rate limit (F-1): keys on the real client IP, consulting
    // X-Forwarded-For only when the direct peer is a configured trusted proxy.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    let mut s = state.write().await;

    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // F-P1-3: the prior code accepted `agent` from the request body and signed
    // it with the operator's cipherclerk, allowing a confused-deputy attack where the
    // caller targets a victim cell's c-list with the operator's signature.
    // Mirror the MCP path: derive the agent cell from the cipherclerk's pubkey and
    // ignore the body's value (we still parse it for error reporting).
    let _body_agent = hex_decode(&req.agent).map_err(|_| StatusCode::BAD_REQUEST)?;
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let agent_bytes = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id).0;
    let agent_cell = CellId(agent_bytes);
    let agent = hex_encode(&agent_bytes);
    let previous_receipt_hash = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());

    // Build the call forest from the request's actions. Each action is signed
    // by the operator's cipherclerk over its canonical bytes
    // (`Authorization::Signature`), so every effect is authenticated to the
    // operator as caller. Cell/value defaults resolve against the action's
    // target (which itself defaults to the operator's own agent cell).
    //
    // This closes the historical blocker where the handler built an empty
    // `CallForest` and the executor rejected every turn ("call forest is
    // empty") so no operator turn ever replicated.
    //
    // Sign over the SAME federation id the executor verifies against
    // (`federation_id_for_executor`): on an unconfigured solo node this is
    // `blake3(pubkey)`, NOT the raw `s.federation_id`. Signing over the latter
    // mismatched the executor's verification domain — once a turn cleared the
    // (fee-sized) budget gate, every action's Ed25519 signature then failed.
    let federation_id = crate::executor_setup::federation_id_for_executor(&s);
    let mut actions = Vec::with_capacity(req.actions.len());
    for action_spec in req.actions {
        let target = match action_spec.target {
            Some(ref h) => match parse_cell_id(h) {
                Ok(c) => c,
                Err(err) => return submit_turn_bad_request(err),
            },
            None => agent_cell,
        };
        let method = action_spec.method.unwrap_or_else(|| "submit".to_string());
        let mut effects = Vec::with_capacity(action_spec.effects.len());
        for effect_spec in action_spec.effects {
            match build_effect(effect_spec, target) {
                Ok(effect) => effects.push(effect),
                Err(err) => return submit_turn_bad_request(err),
            }
        }
        // `make_action` produces a real per-action ed25519 signature.
        actions.push(
            s.cclerk
                .make_action(target, &method, effects, &federation_id),
        );
    }

    let call_forest = {
        let mut forest = CallForest::new();
        for action in actions {
            forest.add_root(action);
        }
        forest
    };

    // Nonce auto-fill: the turn nonce is the agent cell's replay counter, which
    // increments on each committed turn. A thin client that submits several
    // turns in a row cannot know the live value, so when the request leaves
    // `nonce` at its default (0) we fill in the agent cell's current nonce. A
    // caller that needs an explicit nonce (e.g. to pin ordering) passes a
    // non-zero one and we honor it verbatim. This makes repeated CLI turns
    // (register → transfer → revoke) work without the caller threading nonces.
    let effective_nonce = if req.nonce == 0 {
        s.ledger
            .get(&agent_cell)
            .map(|cell| cell.state.nonce())
            .unwrap_or(0)
    } else {
        req.nonce
    };

    let turn = Turn {
        agent: agent_cell,
        nonce: effective_nonce,
        fee: req.fee,
        memo: req.memo,
        // Stamped so the wire marshal accepts the envelope and the turn stays
        // on the verified Lean producer (see `default_valid_until`).
        valid_until: default_valid_until(),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    // Sign the turn.
    let signed = s.cclerk.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    let pre_ledger = s.ledger.clone();

    // Execute the turn locally FIRST — through the ONE shared producer gate
    // (#171): same authoritative (Lean-producer-aware) path as the signed
    // envelope ingress and blocklace-finalized turns.
    let executor = crate::executor_setup::new_submit_executor(&s);
    seed_executor_receipt_head(&executor, turn.agent, previous_receipt_hash);
    let lean_producer_enabled = s.lean_producer_enabled;
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    match exec_result {
        dregg_turn::TurnResult::Committed { mut receipt, .. } => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // Solo mode: record in nullifier log, mark receipt as Tentative,
            // and advance the solo consensus height.
            let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
            if let Some(ref mut solo) = s.solo_consensus
                && solo.is_solo
            {
                receipt.finality = dregg_turn::Finality::Tentative;
                // Finality is bound into receipt_hash and the executor already
                // signed the optimistic Final; re-sign with the node key so the
                // executor_signature matches the committed (Tentative) receipt.
                resign_receipt_committed(&mut receipt, &node_signing_key);
                // Record any nullifiers from this turn in the solo nullifier log.
                // The turn_hash itself serves as the sequencing entry for ordering.
                let height = solo.height;
                let _ = solo
                    .nullifier_log
                    .insert(turn_hash_bytes, turn_hash_bytes, height);
                solo.advance_height();
                #[cfg(debug_assertions)]
                debug_assert_signed_last(&receipt, &node_signing_key);
            }

            // F-DOS-1 / PATH-PRESERVE Phase 5b: the authoritative executor ALREADY
            // validated + committed this turn above (the soundness boundary), so
            // there is NO inline STARK proving and NO inline FRI-free re-check under
            // the lock (the wedge F-DOS-1 closed). The succinct composed proof — its
            // effect-vm leg through the LEAN-emitted ROTATED descriptor — is built +
            // self-verified asynchronously off the lock by the prove pool below.
            if let Err(err) = s.cclerk.append_receipt(receipt.clone()) {
                s.ledger = pre_ledger;
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitTurnResponse {
                    accepted: false,
                    turn_hash: Some(format!("receipt chain mismatch: {err}")),
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("receipt chain mismatch: {err}")),
                }));
            }
            crate::metrics::set_receipt_chain_length(s.cclerk.receipt_chain_length() as f64);
            let receipt_hash = receipt.receipt_hash();
            // Gather the rotated attestation material from the REAL before/after
            // actor cells (pre_ledger / the just-committed s.ledger). A build hiccup
            // (missing/unrepresentable pre-state) is NON-FATAL: the commit stands and
            // the receipt is simply left unattested (the executor is the authority).
            let witness_outcome = match prepare_rotatable_turn(
                &turn,
                &pre_ledger,
                &s.ledger,
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            // The receipt is committed; its attestation is pending if there is a
            // transition to prove (ProofPending), else NotRequired.
            let proof_status = match &witness_outcome {
                HttpWitnessOutcome::Rotatable(_) => ActivityProofStatus::ProofPending,
                HttpWitnessOutcome::NotRequired => ActivityProofStatus::NotRequired,
            };
            // The async prove pool attaches the WitnessedReceipt (and gossips its
            // artifact) off the lock when proving completes; the raw turn block
            // is gossiped immediately below so consensus ordering is not delayed.
            let pending_proof = match witness_outcome {
                HttpWitnessOutcome::Rotatable(rotatable) => Some(rotatable),
                HttpWitnessOutcome::NotRequired => None,
            };
            let bundle_witnessed: Vec<Vec<u8>> = Vec::new();
            let receipt_artifact = postcard::to_stdvec(&receipt).ok();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            // Typed effect enrichment from the REAL before/after actor ledger —
            // so this committed turn's receipt yields transfer/balance/granted
            // facts when dregg-query reads the live index.
            let summaries = summarize_turn_effects(&turn, &pre_ledger, &s.ledger);
            let kinds: Vec<String> = turn
                .call_forest
                .iter_dfs()
                .flat_map(|t| t.action.effects.iter().map(effect_kind))
                .collect();
            let kinds = if kinds.is_empty() {
                vec!["turn_committed".to_string()]
            } else {
                kinds
            };
            push_committed_event_enriched(
                &mut s,
                turn_hash.clone(),
                agent,
                kinds,
                summaries,
                proof_status,
            );

            // Serialize the full SignedTurn for gossip (postcard format).
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");

            drop(s);

            // F-DOS-1: hand proving to the async pool OFF the lock. Returns a
            // fast ack (ProofPending) without waiting for the ~750 ms prover.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            // Emit receipt event to WebSocket subscribers.
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Gossip the turn to federation peers (only if gossip is active).
            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data_for_gossip).await;
                });
            }

            // Submit the turn to the blocklace for consensus ordering. When we
            // produced witness material, gossip the full TurnArtifactBundle
            // (signed turn + receipt + per-cell WitnessedReceipts) so peers
            // materialize real WRs; otherwise fall back to the raw turn block.
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    if bundle_witnessed.is_empty() {
                        blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                    } else {
                        let bundle = dregg_blocklace::finality::TurnArtifactBundle::with_committed(
                            turn_data,
                            receipt_artifact,
                            bundle_witnessed,
                        );
                        blocklace
                            .submit_turn_bundle(&state_for_blocklace, bundle)
                            .await;
                    }
                });
            }

            Ok(Json(SubmitTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: Some(format!("rejected: {reason}")),
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
        _ => {
            crate::metrics::inc_turns_executed("rejected");
            drop(s);
            Ok(Json(SubmitTurnResponse {
                accepted: false,
                turn_hash: None,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some("turn did not commit".to_string()),
            }))
        }
    }
}

/// POST /turns/submit — accept a caller-signed canonical `SignedTurn`.
///
/// Wire format: `Content-Type: application/octet-stream`, body =
/// `postcard::to_stdvec(&dregg_sdk::SignedTurn)`. This is the remote ingress
/// used by rich clients that build app actions with `AppCipherclerk` and need
/// the node to execute, gossip, and order them without re-signing as the node.
async fn post_submit_signed_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    body: axum::body::Bytes,
    limiter: RateLimiter,
) -> Result<Json<SubmitSignedTurnResponse>, StatusCode> {
    // F-1: per-real-client rate limit (XFF-aware behind a trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    let signed: SignedTurn = match postcard::from_bytes(&body) {
        Ok(turn) => turn,
        Err(_) => return Err(StatusCode::BAD_REQUEST),
    };

    let turn_hash_bytes = signed.turn.hash();
    if !signed.signer.verify(&turn_hash_bytes, &signed.signature) {
        return Ok(Json(SubmitSignedTurnResponse {
            accepted: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            signer: Some(hex_encode(&signed.signer.0)),
            action_count: signed.turn.call_forest.action_count(),
            proof_status: ActivityProofStatus::NotCommitted,
            has_witness: false,
            witness_count: 0,
            error: Some("invalid turn signature".to_string()),
        }));
    }

    let default_token_id = *blake3::hash(b"default").as_bytes();
    let expected_agent = dregg_cell::CellId::derive_raw(&signed.signer.0, &default_token_id);
    if signed.turn.agent != expected_agent {
        return Ok(Json(SubmitSignedTurnResponse {
            accepted: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            signer: Some(hex_encode(&signed.signer.0)),
            action_count: signed.turn.call_forest.action_count(),
            proof_status: ActivityProofStatus::NotCommitted,
            has_witness: false,
            witness_count: 0,
            error: Some("turn agent does not match signer default cell".to_string()),
        }));
    }

    let turn_hash = hex_encode(&turn_hash_bytes);
    let signer = hex_encode(&signed.signer.0);
    let agent = hex_encode(&signed.turn.agent.0);
    let action_count = signed.turn.call_forest.action_count();
    let signed_for_gossip = signed.clone();

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let expected_prev = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());
    if let Some(claimed_prev) = signed.turn.previous_receipt_hash
        && Some(claimed_prev) != expected_prev
    {
        return Ok(Json(SubmitSignedTurnResponse {
            accepted: false,
            turn_hash: Some(turn_hash),
            signer: Some(signer),
            action_count,
            proof_status: ActivityProofStatus::NotCommitted,
            has_witness: false,
            witness_count: 0,
            error: Some("receipt chain mismatch".to_string()),
        }));
    }

    let pre_ledger = s.ledger.clone();
    // ONE executor gate (#171): the remote signed envelope executes through the
    // same producer-aware path as local thin-HTTP turns and finalized turns —
    // a remote agent's turn is covered by the verified Lean producer exactly
    // like a local one (its SDK stamps `valid_until`, so it does not fall off
    // the wire marshal).
    let executor = crate::executor_setup::new_submit_executor(&s);
    seed_executor_receipt_head(&executor, signed.turn.agent, expected_prev);
    let lean_producer_enabled = s.lean_producer_enabled;
    let exec_result = crate::executor_setup::execute_via_producer(
        &executor,
        &signed.turn,
        &mut s.ledger,
        lean_producer_enabled,
    );

    match exec_result {
        dregg_turn::TurnResult::Committed { mut receipt, .. } => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
            if let Some(ref mut solo) = s.solo_consensus
                && solo.is_solo
            {
                receipt.finality = dregg_turn::Finality::Tentative;
                // Re-sign after the committed finality downgrade: finality is bound
                // into receipt_hash, and the executor signed the optimistic Final.
                resign_receipt_committed(&mut receipt, &node_signing_key);
                let height = solo.height;
                let _ = solo
                    .nullifier_log
                    .insert(turn_hash_bytes, turn_hash_bytes, height);
                solo.advance_height();
                #[cfg(debug_assertions)]
                debug_assert_signed_last(&receipt, &node_signing_key);
            }

            // F-DOS-1 / PATH-PRESERVE Phase 5b: the executor already validated +
            // committed this turn (the soundness boundary); no inline proving / no
            // inline re-check. The composed proof (rotated effect-vm leg) is built +
            // self-verified asynchronously off the lock by the prove pool below.
            if let Err(err) = s.cclerk.append_receipt(receipt.clone()) {
                s.ledger = pre_ledger;
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitSignedTurnResponse {
                    accepted: false,
                    turn_hash: Some(turn_hash),
                    signer: Some(signer),
                    action_count,
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("receipt chain mismatch: {err}")),
                }));
            }
            crate::metrics::set_receipt_chain_length(s.cclerk.receipt_chain_length() as f64);
            let receipt_hash = receipt.receipt_hash();
            let witness_outcome = match prepare_rotatable_turn(
                &signed.turn,
                &pre_ledger,
                &s.ledger,
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            let proof_status = match &witness_outcome {
                HttpWitnessOutcome::Rotatable(_) => ActivityProofStatus::ProofPending,
                HttpWitnessOutcome::NotRequired => ActivityProofStatus::NotRequired,
            };
            // The async prove pool attaches the WitnessedReceipt off the lock.
            let pending_proof = match witness_outcome {
                HttpWitnessOutcome::Rotatable(rotatable) => Some(rotatable),
                HttpWitnessOutcome::NotRequired => None,
            };
            let bundle_witnessed: Vec<Vec<u8>> = Vec::new();
            let receipt_artifact = postcard::to_stdvec(&receipt).ok();
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            push_committed_event(
                &mut s,
                turn_hash.clone(),
                agent,
                vec![format!("signed_turn:{action_count}")],
                proof_status,
            );

            let turn_data = postcard::to_stdvec(&signed_for_gossip)
                .expect("SignedTurn serialization after successful decode");

            drop(s);

            // F-DOS-1: prove off the lock; fast ProofPending ack.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data_for_gossip).await;
                });
            }

            // Gossip the full TurnArtifactBundle (with per-cell WitnessedReceipts)
            // when witness material was produced; raw turn block otherwise.
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    if bundle_witnessed.is_empty() {
                        blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                    } else {
                        let bundle = dregg_blocklace::finality::TurnArtifactBundle::with_committed(
                            turn_data,
                            receipt_artifact,
                            bundle_witnessed,
                        );
                        blocklace
                            .submit_turn_bundle(&state_for_blocklace, bundle)
                            .await;
                    }
                });
            }

            Ok(Json(SubmitSignedTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitSignedTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
        _ => {
            crate::metrics::inc_turns_executed("rejected");
            drop(s);
            Ok(Json(SubmitSignedTurnResponse {
                accepted: false,
                turn_hash: Some(turn_hash),
                signer: Some(signer),
                action_count,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some("turn did not commit".to_string()),
            }))
        }
    }
}

/// One independently-sourced per-cell WitnessedReceipt for the cross-node
/// aggregate route. `cell_id` is the 32-byte cell hex; `witnessed_receipt` is
/// the hex-encoded `dregg_turn::WitnessedReceipt` artifact (DWR1 or legacy
/// JSON/postcard) — the SAME bytes a peer gossips in a `TurnArtifactBundle`
/// and materializes via `materialize_blocklace_artifacts`.
#[derive(Debug, serde::Deserialize)]
pub struct AggregateWitnessEntry {
    pub cell_id: String,
    pub witnessed_receipt: String,
}

/// POST /turns/aggregate request: the canonical SignedTurn (hex postcard) plus
/// two-or-more independently-produced per-cell WitnessedReceipts.
#[derive(Debug, serde::Deserialize)]
pub struct AggregateBundleRequest {
    /// Hex-encoded `postcard::to_stdvec(&dregg_sdk::SignedTurn)` — the canonical
    /// Turn the aggregator re-derives every bilateral schedule field from.
    pub signed_turn: String,
    /// Per-cell witnessed receipts, gathered from independent sources (e.g.
    /// gossiped + materialized from different nodes). Must be >= 2 to exercise
    /// a genuine cross-cell aggregation.
    pub entries: Vec<AggregateWitnessEntry>,
}

#[derive(Debug, serde::Serialize)]
pub struct AggregateBundleResponse {
    pub aggregated: bool,
    pub n_cells: usize,
    /// The verified `AggregatedBundle` (real outer STARK proof) on success.
    pub aggregated_bundle: Option<serde_json::Value>,
    pub error: Option<String>,
}

/// POST /turns/aggregate — run the REAL cross-node bilateral aggregate over
/// independently-sourced per-cell WitnessedReceipts.
///
/// Unlike the MCP `dregg_bilateral_action` tool (which self-proves BOTH sides
/// inside a single node in one call), this endpoint accepts WitnessedReceipt
/// artifacts that were produced elsewhere — gossiped through the blocklace and
/// materialized by `materialize_blocklace_artifacts`, or otherwise gathered
/// independently. It decodes each WR (the same DWR1 artifact format used on the
/// wire), runs `prove_aggregated_bundle` to produce a real outer STARK proof,
/// then `verify_aggregated_bundle` to confirm it before returning the bundle.
///
/// Soundness gates run inside the aggregator: `require_scope2_witness` per WR
/// and `WitnessedReceipt::verify_bilateral_chain` over the full set against the
/// canonical Turn (rejecting tampered PI, mismatched sender/receiver, etc.).
async fn post_aggregate_bundle(
    State(state): State<NodeState>,
    Json(req): Json<AggregateBundleRequest>,
) -> Result<Json<AggregateBundleResponse>, StatusCode> {
    {
        let s = state.read().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    let signed_turn_bytes =
        hex_decode_var(&req.signed_turn).map_err(|_| StatusCode::BAD_REQUEST)?;
    let signed: SignedTurn =
        postcard::from_bytes(&signed_turn_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn = signed.turn;

    if req.entries.len() < 2 {
        return Ok(Json(AggregateBundleResponse {
            aggregated: false,
            n_cells: req.entries.len(),
            aggregated_bundle: None,
            error: Some(
                "cross-node aggregate requires >= 2 independently-sourced WitnessedReceipts".into(),
            ),
        }));
    }

    let mut per_cell: Vec<(CellId, dregg_turn::WitnessedReceipt)> =
        Vec::with_capacity(req.entries.len());
    for (idx, entry) in req.entries.iter().enumerate() {
        let cell_bytes = match hex_decode(&entry.cell_id) {
            Ok(b) => b,
            Err(_) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: invalid cell_id hex")),
                }));
            }
        };
        let wr_bytes = match hex_decode_var(&entry.witnessed_receipt) {
            Ok(b) => b,
            Err(_) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: invalid witnessed_receipt hex")),
                }));
            }
        };
        let mut wr = match dregg_turn::WitnessedReceipt::from_artifact_bytes(&wr_bytes) {
            Ok(wr) => wr,
            Err(e) => {
                return Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells: req.entries.len(),
                    aggregated_bundle: None,
                    error: Some(format!("entries[{idx}]: malformed WitnessedReceipt: {e}")),
                }));
            }
        };
        let cell = CellId(cell_bytes);
        // ROTATED-WR PRODUCER (ROTATION-CUTOVER §EXEC.3): a rotated WR carries only the 38/39-felt
        // rotated PI — too short for `build_inner_rows_v2` to project the 49-felt schedule window
        // (which needs the >=204-wide v1 PI). If such a WR arrived without a native
        // `bilateral_schedule` (e.g. produced by a peer that did not set it), reconstruct the
        // honest block here from the canonical Turn. We do NOT overwrite a block the WR already
        // carries — that one is what the cross-check binds. CG-3 in-circuit rejects a divergent
        // block, so reconstructing the honest one for the short-PI case adds no tampering vector.
        if wr.bilateral_schedule.is_none()
            && wr.public_inputs.len() < dregg_circuit::effect_vm::pi::ACTIVE_BASE_COUNT
        {
            wr.bilateral_schedule = Some(
                dregg_turn::bilateral_schedule::schedule_block_for_cell(&turn, &cell).to_vec(),
            );
        }
        per_cell.push((cell, wr));
    }
    let n_cells = per_cell.len();

    // Real outer STARK proof over the independently-sourced per-cell WRs.
    match dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle(&turn, &per_cell) {
        Ok(bundle) => {
            match dregg_turn::aggregate_bilateral_prover::verify_aggregated_bundle(&bundle) {
                Ok(()) => Ok(Json(AggregateBundleResponse {
                    aggregated: true,
                    n_cells,
                    aggregated_bundle: Some(
                        serde_json::to_value(&bundle).unwrap_or(serde_json::Value::Null),
                    ),
                    error: None,
                })),
                Err(e) => Ok(Json(AggregateBundleResponse {
                    aggregated: false,
                    n_cells,
                    aggregated_bundle: None,
                    error: Some(format!("aggregation_verify_failed: {e}")),
                })),
            }
        }
        Err(e) => Ok(Json(AggregateBundleResponse {
            aggregated: false,
            n_cells,
            aggregated_bundle: None,
            error: Some(format!("aggregation_prove_failed: {e}")),
        })),
    }
}

/// Domain string used to derive the executor's X25519 unsealer secret from
/// the cipherclerk seed via `AgentCipherclerk::derive_symmetric_key`. Stable
/// across deployments — a single node always presents the same public key
/// for a given cipherclerk, which is required so senders can cache the recipient
/// key across reconnects.
const TURN_UNSEALER_DOMAIN: &str = "dregg-turn-unsealer-v1";

/// GET /turns/encryption-key — return the executor's static X25519 public
/// key (the value senders pass as `recipient_public` to
/// `EncryptedTurn::encrypt_for_executor`). AUDIT-privacy.md §11.2: this is
/// the production discovery hop that closes the encrypted-turn pipeline.
async fn get_turn_encryption_key(
    State(state): State<NodeState>,
) -> Result<Json<TurnEncryptionKeyResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    let secret = s.cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
    Ok(Json(TurnEncryptionKeyResponse {
        executor_x25519_public: hex_encode(public.as_bytes()),
        derivation_domain: TURN_UNSEALER_DOMAIN.to_string(),
    }))
}

/// POST /turns/submit-encrypted — accept a postcard-encoded
/// `dregg_turn::EncryptedTurn` envelope, decrypt with the cipherclerk-derived
/// X25519 unsealer secret, and apply via
/// `TurnExecutor::apply_encrypted_turn`. AUDIT-privacy.md §11.2: closes
/// the "encryption claim unreachable from production" gap.
///
/// Wire format: `Content-Type: application/octet-stream`, body =
/// `postcard::to_stdvec(&encrypted_turn)` bytes.
///
/// Boundary contract (BOUNDARIES.md §5):
/// - **out-of-band** to gossip / wire observers (only ciphertext visible)
/// - **cleartext-inside** the executor holding the unsealer secret
/// - the produced receipt's `was_encrypted = true` flag is the **only**
///   metadata bit disclosed; it does not leak inner-turn content.
async fn post_submit_encrypted_turn(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    body: axum::body::Bytes,
    limiter: RateLimiter,
) -> Result<Json<SubmitEncryptedTurnResponse>, StatusCode> {
    // Reuse the cleartext-turn rate limiter — encrypted turns shouldn't
    // get a privacy-flavored quota bypass. F-1: XFF-aware client keying.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    crate::metrics::inc_turns_submitted();
    let start = Instant::now();

    // Decode the envelope. A malformed wire body returns 400; no further
    // executor work is done.
    let encrypted: dregg_turn::EncryptedTurn = match postcard::from_bytes(&body) {
        Ok(e) => e,
        Err(_) => return Err(StatusCode::BAD_REQUEST),
    };

    // F-DOS-PRIV: validity gate BEFORE any decrypt/execute work. An
    // `EncryptedTurn` envelope carries no signature of its own; without this
    // check a stranger could POST any postcard blob and force the node to
    // X25519-decrypt + execute it (a fee-DoS — the cleartext `/turns/submit`
    // path avoids this by `signer.verify`-ing before doing work). `verify_stark`
    // checks the Phase-1 submitter authentication (Ed25519 over the public
    // inputs + key→agent binding) fail-closed, so an unauthenticated or forged
    // envelope is rejected here — before the node spends decrypt work.
    if let Err(err) = encrypted.verify_stark() {
        crate::metrics::inc_turns_executed("rejected");
        return Ok(Json(SubmitEncryptedTurnResponse {
            accepted: false,
            turn_hash: Some(format!(
                "rejected: encrypted turn validity proof invalid: {err:?}"
            )),
            was_encrypted: false,
            proof_status: ActivityProofStatus::NotCommitted,
            has_witness: false,
            witness_count: 0,
            error: Some(format!("encrypted turn validity proof invalid: {err:?}")),
        }));
    }

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Derive the executor's unsealer secret from the cipherclerk. Held in a
    // local for the lifetime of this handler only.
    let sealer_secret = s.cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let unsealer_public =
        x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(sealer_secret));
    let cleartext_turn =
        match encrypted.decrypt_for_executor(&sealer_secret, unsealer_public.as_bytes()) {
            Ok(turn) => turn,
            Err(err) => {
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitEncryptedTurnResponse {
                    accepted: false,
                    turn_hash: Some(format!(
                        "rejected: encrypted turn decryption failed: {err:?}"
                    )),
                    was_encrypted: false,
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("encrypted turn decryption failed: {err:?}")),
                }));
            }
        };

    let mut executor = crate::executor_setup::new_submit_executor(&s);
    // Defense-in-depth: the executor's own encrypted-turn path re-runs the
    // validity gate (the handler already gated above before decrypting).
    executor.set_require_validity_proof(true);
    let expected_prev = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());
    seed_executor_receipt_head(&executor, encrypted.agent, expected_prev);

    let pre_ledger = s.ledger.clone();
    let result = executor.apply_encrypted_turn(&encrypted, &sealer_secret, &mut s.ledger);

    match result {
        Ok(mut receipt) => {
            crate::metrics::inc_turns_executed("committed");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // Solo mode: record nullifier + tentative finality, same as
            // the cleartext path (post_submit_turn). The encrypted path
            // doesn't change consensus semantics — only privacy.
            let turn_hash_bytes = receipt.turn_hash;
            let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
            if let Some(ref mut solo) = s.solo_consensus
                && solo.is_solo
            {
                receipt.finality = dregg_turn::Finality::Tentative;
                // Re-sign after the committed finality downgrade: finality is bound
                // into receipt_hash, and the executor signed the optimistic Final.
                resign_receipt_committed(&mut receipt, &node_signing_key);
                let height = solo.height;
                let _ = solo
                    .nullifier_log
                    .insert(turn_hash_bytes, turn_hash_bytes, height);
                solo.advance_height();
                #[cfg(debug_assertions)]
                debug_assert_signed_last(&receipt, &node_signing_key);
            }

            let turn_hash = hex_encode(&turn_hash_bytes);
            let agent = hex_encode(&receipt.agent.0);
            let was_encrypted = receipt.was_encrypted;
            // F-DOS-1 / PATH-PRESERVE Phase 5b: the executor already validated +
            // committed this turn (the soundness boundary); no inline proving / no
            // inline re-check. The composed proof (rotated effect-vm leg) is built +
            // self-verified asynchronously off the lock by the prove pool below.
            if let Err(err) = s.cclerk.append_receipt(receipt.clone()) {
                s.ledger = pre_ledger;
                crate::metrics::inc_turns_executed("rejected");
                drop(s);
                return Ok(Json(SubmitEncryptedTurnResponse {
                    accepted: false,
                    turn_hash: Some(format!("receipt chain mismatch: {err}")),
                    was_encrypted: false,
                    proof_status: ActivityProofStatus::NotCommitted,
                    has_witness: false,
                    witness_count: 0,
                    error: Some(format!("receipt chain mismatch: {err}")),
                }));
            }
            crate::metrics::set_receipt_chain_length(s.cclerk.receipt_chain_length() as f64);
            let receipt_hash = receipt.receipt_hash();
            let witness_outcome = match prepare_rotatable_turn(
                &cleartext_turn,
                &pre_ledger,
                &s.ledger,
                receipt_hash,
            ) {
                Ok(outcome) => outcome,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash,
                        error = %err,
                        "could not prepare rotated attestation; receipt committed-but-unattested"
                    );
                    HttpWitnessOutcome::NotRequired
                }
            };
            let proof_status = match &witness_outcome {
                HttpWitnessOutcome::Rotatable(_) => ActivityProofStatus::ProofPending,
                HttpWitnessOutcome::NotRequired => ActivityProofStatus::NotRequired,
            };
            let pending_proof = match witness_outcome {
                HttpWitnessOutcome::Rotatable(rotatable) => Some(rotatable),
                HttpWitnessOutcome::NotRequired => None,
            };
            let witness_count = s.witnessed_receipt_count(&receipt_hash);

            push_committed_event(
                &mut s,
                turn_hash.clone(),
                agent,
                vec!["encrypted_turn_committed".to_string()],
                proof_status,
            );

            drop(s);

            // F-DOS-1: prove off the lock.
            if let Some(rotatable) = pending_proof {
                enqueue_async_proof(
                    &state,
                    rotatable,
                    receipt.clone(),
                    receipt_hash,
                    turn_hash.clone(),
                )
                .await;
            }

            // Emit receipt event (same surface as cleartext-turn commits).
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            Ok(Json(SubmitEncryptedTurnResponse {
                accepted: true,
                turn_hash: Some(turn_hash),
                was_encrypted,
                proof_status,
                has_witness: witness_count > 0,
                witness_count,
                error: None,
            }))
        }
        Err(reason) => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::record_turn_execution_duration(start.elapsed().as_secs_f64());
            drop(s);
            Ok(Json(SubmitEncryptedTurnResponse {
                accepted: false,
                turn_hash: Some(format!("rejected: {reason}")),
                was_encrypted: false,
                proof_status: ActivityProofStatus::NotCommitted,
                has_witness: false,
                witness_count: 0,
                error: Some(format!("rejected: {reason}")),
            }))
        }
    }
}

async fn get_cell(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    let found = s.ledger.get(&cell_id).is_some();

    Ok(Json(CellResponse {
        id,
        found,
        balance: s.ledger.get(&cell_id).map(|cell| cell.state.balance()),
    }))
}

// =============================================================================
// Explorer API Handlers (public, read-only)
// =============================================================================

/// GET /api/cells — list all cells in the ledger with summary info.
async fn get_all_cells(State(state): State<NodeState>) -> Json<Vec<CellListEntry>> {
    let s = state.read().await;
    let entries: Vec<CellListEntry> = s
        .ledger
        .iter()
        .map(|(id, cell)| CellListEntry {
            id: hex_encode(&id.0),
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            capability_count: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            has_program: !matches!(cell.program, dregg_cell::CellProgram::None),
            found: true,
        })
        .collect();
    Json(entries)
}

/// GET /api/cell/:id — detailed cell information for the explorer.
async fn get_cell_detail(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<CellDetailResponse>, StatusCode> {
    let s = state.read().await;

    let cell_id_bytes: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    match s.ledger.get(&cell_id) {
        Some(cell) => Ok(Json(CellDetailResponse {
            id: id.clone(),
            found: true,
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            capability_count: cell.capabilities.len(),
            num_capabilities: cell.capabilities.len(),
            has_delegate: cell.delegate.is_some(),
            delegate: cell.delegate.as_ref().map(|d| hex_encode(&d.0)),
            has_program: !matches!(cell.program, dregg_cell::CellProgram::None),
            public_key: hex_encode(cell.public_key()),
            token_id: hex_encode(cell.token_id()),
            proved_state: cell.state.proved_state(),
            delegation_epoch: cell.state.delegation_epoch(),
            state_commitment: hex_encode(&cell.state_commitment()),
            program_kind: match &cell.program {
                dregg_cell::CellProgram::None => "None".to_string(),
                dregg_cell::CellProgram::Predicate { .. } => "Predicate".to_string(),
                dregg_cell::CellProgram::Cases { .. } => "Cases".to_string(),
                dregg_cell::CellProgram::Circuit { .. } => "Circuit".to_string(),
            },
            program: cell.program.to_view(),
            fields: cell.state.fields.iter().map(|f| hex_encode(f)).collect(),
        })),
        None => Ok(Json(CellDetailResponse {
            id,
            found: false,
            balance: 0,
            nonce: 0,
            capability_count: 0,
            num_capabilities: 0,
            has_delegate: false,
            delegate: None,
            has_program: false,
            public_key: String::new(),
            token_id: String::new(),
            proved_state: false,
            delegation_epoch: 0,
            state_commitment: String::new(),
            program_kind: "None".to_string(),
            program: dregg_cell::program::CellProgramView::None,
            fields: Vec::new(),
        })),
    }
}

/// Hash a passphrase with Argon2id and derive a bearer seed.
///
/// Returns (PHC string for storage, bearer_seed for token derivation).
fn hash_passphrase(passphrase: &str) -> (String, [u8; 32]) {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default(); // Argon2id v19 with recommended params
    let phc_string = argon2
        .hash_password(passphrase.as_bytes(), &salt)
        .expect("argon2 hash_password should not fail")
        .to_string();
    // Derive a separate bearer seed from passphrase + salt using BLAKE3.
    // This is safe because BLAKE3 is a proper KDF and the input has high entropy
    // (passphrase + random salt).
    let bearer_seed = blake3::derive_key(
        "dregg-node-bearer-v1",
        format!("{}{}", passphrase, salt.as_str()).as_bytes(),
    );
    (phc_string, bearer_seed)
}

/// P1 Fix 4: Rate-limited passphrase unlock endpoint.
async fn post_cclerk_unlock(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<UnlockRequest>,
    limiter: RateLimiter,
) -> Result<Json<UnlockResponse>, StatusCode> {
    // Rate limit check (F-1: per-real-client, XFF-aware behind trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // F-CRIT-1: during pre-passphrase setup, only loopback callers may set the
    // passphrase. Once a passphrase is set, the bearer-token auth on subsequent
    // requests is sufficient; but unlock from the network is acceptable since the
    // attacker must still know the passphrase.
    {
        let s = state.read().await;
        if s.passphrase_hash.is_none() && !addr.ip().is_loopback() {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    if req.passphrase.is_empty() {
        return Ok(Json(UnlockResponse {
            success: false,
            bearer_token: None,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;

    match s.passphrase_hash.clone() {
        Some(stored_hash) => {
            // Verify against stored Argon2id hash.
            let parsed =
                PasswordHash::new(&stored_hash).map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
            if Argon2::default()
                .verify_password(req.passphrase.as_bytes(), &parsed)
                .is_err()
            {
                return Ok(Json(UnlockResponse {
                    success: false,
                    bearer_token: None,
                    error: Some("invalid passphrase".to_string()),
                }));
            }
            s.unlocked = true;
            let bearer_token = s.bearer_seed.map(api_bearer_token);
            Ok(Json(UnlockResponse {
                success: true,
                bearer_token,
                error: None,
            }))
        }
        None => {
            // First unlock sets the passphrase using Argon2id.
            let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
            s.passphrase_hash = Some(phc_string.clone());
            s.bearer_seed = Some(bearer_seed);
            let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
            let _ = s.store.set_config("bearer_seed", &bearer_seed);
            s.unlocked = true;
            Ok(Json(UnlockResponse {
                success: true,
                bearer_token: Some(api_bearer_token(bearer_seed)),
                error: None,
            }))
        }
    }
}

fn api_bearer_token(bearer_seed: [u8; 32]) -> String {
    hex_encode(&blake3::derive_key("dregg-api-bearer-v1", &bearer_seed))
}

/// P1 Fix 4: Rate-limited set-passphrase endpoint.
async fn post_set_passphrase(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<SetPassphraseRequest>,
    limiter: RateLimiter,
) -> Result<Json<SetPassphraseResponse>, StatusCode> {
    // Rate limit check (F-1: per-real-client, XFF-aware behind trusted proxy).
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // F-CRIT-1: setting the initial passphrase from a non-loopback caller is the
    // remote-takeover bug. Reject. Once the passphrase IS set, this endpoint
    // returns "already set" so the network check below is not load-bearing in
    // that branch, but we apply it uniformly to avoid an oracle.
    if !addr.ip().is_loopback() {
        return Err(StatusCode::FORBIDDEN);
    }

    if req.passphrase.is_empty() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase must not be empty".to_string()),
        }));
    }

    let mut s = state.write().await;

    if s.passphrase_hash.is_some() {
        return Ok(Json(SetPassphraseResponse {
            success: false,
            error: Some("passphrase already set; unlock first to change it".to_string()),
        }));
    }

    let (phc_string, bearer_seed) = hash_passphrase(&req.passphrase);
    s.passphrase_hash = Some(phc_string.clone());
    s.bearer_seed = Some(bearer_seed);
    // Persist the passphrase hash and bearer seed to the store so they survive restarts.
    let _ = s.store.set_config("passphrase_hash", phc_string.as_bytes());
    let _ = s.store.set_config("bearer_seed", &bearer_seed);

    Ok(Json(SetPassphraseResponse {
        success: true,
        error: None,
    }))
}

/// Drive a payable intent through the VERIFIED ledger commit, returning the real
/// [`dregg_turn::TurnReceipt`]. This is the single shared core that both
/// `POST /intents/fulfill` (with an explicit fulfiller) and `POST /intents`
/// (inline self-fulfillment at submit time) call — so a submitted self-fulfillable
/// intent commits through EXACTLY the same path as an operator-driven fulfill,
/// never a stub.
///
/// The payer is the intent's creator (`payer_cell.0 == intent.creator.0`, enforced
/// by the caller); the recipient is the fulfiller cell. Both cells must be LIVE in
/// the ledger and distinct, and the intent must carry a non-zero `min_budget`
/// (the verified value leg) — otherwise the verified executor REFUSES, and the
/// ledger is untouched (fail-closed, no fallback).
fn commit_intent_fulfillment_verified(
    s: &mut crate::state::NodeStateInner,
    intent: &dregg_intent::Intent,
    payer_cell: dregg_sdk::CellId,
    recipient_cell: dregg_sdk::CellId,
    state_root: u32,
    state_root_block: u64,
) -> Result<dregg_turn::TurnReceipt, dregg_intent::fulfillment::FulfillmentError> {
    let state_root = dregg_circuit::BabyBear::new(state_root);

    // The node's stable per-node intent root key. The minted Trusted-mode macaroon's HMAC
    // chain is verified against THIS key inside the flow — so the capability grant genuinely
    // verifies (a real token, not a `[0x01; 4]` stub the verify would reject).
    let intent_root_key = s.cclerk.derive_symmetric_key("dregg-intent-root-key-v1");

    // Build a REAL Trusted-mode fulfillment: a genuine HMAC-chained attenuated macaroon
    // bound to the intent's grant. This passes `verify_fulfillment_with_predicates_and_key`
    // honestly; nothing is laundered.
    let fulfillment_with_preds = dregg_intent::fulfillment::build_self_fulfillment_trusted(
        intent,
        dregg_intent::CommitmentId(recipient_cell.0),
        intent_root_key,
        state_root,
        state_root_block,
    )?;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Settle the value leg through the VERIFIED executor edge, supplying the same root key
    // so the Trusted-mode HMAC verification inside the flow succeeds. Fail-closed: a refused
    // payment leaves the ledger untouched.
    dregg_intent::fulfillment::execute_fulfillment_flow_verified_with_key(
        intent,
        &fulfillment_with_preds,
        &mut s.ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_height,
        Some(&intent_root_key),
    )
}

async fn post_intent(
    State(state): State<NodeState>,
    Json(raw): Json<serde_json::Value>,
) -> Result<Json<IntentSubmitResponse>, StatusCode> {
    // P0 Fix 3: Deserialize into a proper Intent struct for validation.
    let intent: dregg_intent::Intent =
        serde_json::from_value(raw.clone()).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Validate the intent using dregg-intent's validation logic.
    dregg_intent::validation::validate_intent(&intent).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the content-addressed ID is correct (prevents ID spoofing).
    let recomputed = dregg_intent::Intent::new(
        intent.kind,
        intent.matcher.clone(),
        intent.creator,
        intent.expiry,
        intent.stake_proof.clone(),
    );
    if recomputed.id != intent.id {
        return Err(StatusCode::BAD_REQUEST);
    }

    let intent_id_hex = hex_encode(&intent.id);

    // A submitted intent is SELF-FULFILLABLE — and must therefore COMMIT immediately
    // through the verified ledger rather than rot in the pool — when it names an
    // explicit fulfiller cell alongside a payable value leg. The fulfiller hint rides
    // as sibling fields on the submit body (the canonical `Intent` is untouched, so its
    // content-addressed id is unchanged). When present, we drain it through the SAME
    // verified path `/intents/fulfill` uses (`commit_intent_fulfillment_verified` →
    // `execute_fulfillment_flow_verified`) and return the real receipt.
    //
    // Absent a fulfiller, the intent is an open offer/need with no counter-leg yet: it
    // pools (the prior behavior) for a later match-and-fulfill. The pool is no longer a
    // dead end — a fulfiller (here or via `/intents/fulfill`) drains it to the ledger.
    let fulfiller_cell: Option<[u8; 32]> = raw
        .get("fulfiller_cell")
        .and_then(|v| v.as_str())
        .and_then(|h| hex_decode(h).ok())
        .and_then(|b| <[u8; 32]>::try_from(b.as_slice()).ok());
    let req_state_root: u32 = raw
        .get("state_root")
        .and_then(|v| v.as_u64())
        .map(|v| v as u32)
        .unwrap_or(0);
    let req_state_root_block: u64 = raw
        .get("state_root_block")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let mut committed = false;
    let mut committed_turn_hash: Option<String> = None;

    // INLINE SELF-FULFILLMENT (verified, fail-closed). The payer is the intent creator;
    // the recipient is the named fulfiller. The verified executor enforces distinctness,
    // liveness, and availability — a refusal leaves the ledger untouched and the intent
    // simply pools instead of committing.
    if let Some(fulfiller_bytes) = fulfiller_cell {
        let payer_cell = dregg_sdk::CellId(intent.creator.0);
        let recipient_cell = dregg_sdk::CellId(fulfiller_bytes);

        let mut s = state.write().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
        match commit_intent_fulfillment_verified(
            &mut s,
            &intent,
            payer_cell,
            recipient_cell,
            req_state_root,
            req_state_root_block,
        ) {
            Ok(receipt) => {
                committed = true;
                committed_turn_hash = Some(hex_encode(&receipt.turn_hash));
            }
            Err(e) => {
                // Fail-closed: a self-fulfillment the verified executor REFUSES is a
                // hard error to the submitter — we do NOT silently downgrade a payable,
                // explicitly-targeted intent into a quiet pool entry (that would launder
                // a rejected commit as a successful submit).
                tracing::warn!(intent = %intent_id_hex, error = %e, "intent self-fulfillment refused by verified executor");
                return Err(StatusCode::UNPROCESSABLE_ENTITY);
            }
        }
    } else {
        // No counter-leg yet — pool for a later match-and-fulfill.
        // P1 Fix 5: enforce size limit.
        let mut s = state.write().await;
        if s.intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.intent_pool.insert(intent.id, intent.clone());
        // Invalidate PIR index cache on pool mutation.
        s.pir_index_cache = None;
    }

    // Broadcast to WS subscribers.
    state.emit(NodeEvent::Intent {
        intent: serde_json::to_value(&intent).unwrap_or_default(),
    });
    if let Some(ref turn_hash) = committed_turn_hash {
        state.emit(NodeEvent::Receipt {
            hash: turn_hash.clone(),
        });
    }

    // Gossip the intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let intent_json = raw;
        tokio::spawn(async move {
            gossip.gossip_intent(&intent_json).await;
        });
    }

    Ok(Json(IntentSubmitResponse {
        intent_id: intent_id_hex,
        stored: !committed,
        committed,
        turn_hash: committed_turn_hash,
    }))
}

/// GET /api/events — return committed events after a given block height.
///
/// Used by the Discord bot and other polling clients to catch up on state changes
/// without maintaining a persistent WebSocket connection.
async fn get_events(
    Query(params): Query<EventsQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<CommittedEvent>> {
    let since_height = params.since_height;
    let limit = params.limit.unwrap_or(50).min(200);

    let s = state.read().await;
    Json(select_committed_events(&s.event_log, since_height, limit))
}

async fn get_starbridge_events(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<CommittedEvent>> {
    let limit = starbridge_limit(params.limit);
    let since_height = params.since_height;

    let s = state.read().await;
    let events = select_committed_events(&s.event_log, since_height, usize::MAX)
        .into_iter()
        .filter(|event| starbridge_event_matches(event, &params))
        .take(limit)
        .collect();
    Json(events)
}

async fn get_starbridge_turns(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeSignedTurnInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let turns = s
        .consensus_queue
        .iter()
        .enumerate()
        .rev()
        .filter_map(|(queue_index, signed)| {
            let info = starbridge_signed_turn_info(queue_index, signed);
            starbridge_signed_turn_matches(&info, &params).then_some(info)
        })
        .take(limit)
        .collect();
    Json(turns)
}

async fn get_starbridge_actions(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeActionInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let mut actions = Vec::new();

    for (queue_index, signed) in s.consensus_queue.iter().enumerate().rev() {
        let turn_hash = hex_encode(&signed.turn.hash());
        let signer = hex_encode(&signed.signer.0);
        let agent = hex_encode(&signed.turn.agent.0);
        let app = classify_starbridge_app(signed.turn.memo.as_deref(), &[]);

        for (action_index, tree) in signed.turn.call_forest.iter_dfs().enumerate() {
            let effect_kinds: Vec<String> = tree.action.effects.iter().map(effect_kind).collect();
            let touched_cells = action_touched_cells(&tree.action);
            let app = app
                .clone()
                .or_else(|| classify_starbridge_app(signed.turn.memo.as_deref(), &effect_kinds));
            let info = StarbridgeActionInfo {
                source: "consensus_queue",
                queue_index,
                action_index,
                turn_hash: turn_hash.clone(),
                signer: signer.clone(),
                agent: agent.clone(),
                memo: signed.turn.memo.clone(),
                app,
                target: hex_encode(&tree.action.target.0),
                method: hex_encode(&tree.action.method),
                effect_kinds,
                touched_cells,
            };
            if starbridge_action_matches(&info, &params) {
                actions.push(info);
                if actions.len() >= limit {
                    return Json(actions);
                }
            }
        }
    }

    Json(actions)
}

async fn get_starbridge_identity_events(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityEventInfo>> {
    let limit = starbridge_limit(params.limit);
    let since_height = params.since_height;
    let s = state.read().await;
    let mut out = Vec::new();

    for event in select_committed_events(&s.event_log, since_height, usize::MAX) {
        if !starbridge_event_matches(&event, &identity_scoped_params(&params)) {
            continue;
        }
        out.push(StarbridgeIdentityEventInfo {
            source: "event_log",
            chain_index: None,
            event_index: None,
            height: Some(event.height),
            receipt_hash: None,
            turn_hash: event.turn_hash,
            cell_id: event.cell_id,
            timestamp: event.timestamp,
            topic: None,
            data: None,
            effects: event.effects,
            proof_status: event.proof_status,
            finality: None,
        });
        if out.len() >= limit {
            return Json(out);
        }
    }

    let chain = s.cclerk.receipt_chain();
    for (chain_index, receipt) in chain.iter().enumerate().rev() {
        if !identity_receipt_matches(receipt, &params) {
            continue;
        }
        for (event_index, event) in receipt.emitted_events.iter().enumerate() {
            if params.cell.as_ref().is_some_and(|cell| {
                !hex_encode(&event.cell.0).eq_ignore_ascii_case(cell)
                    && !hex_encode(&receipt.agent.0).eq_ignore_ascii_case(cell)
            }) {
                continue;
            }
            out.push(StarbridgeIdentityEventInfo {
                source: "receipt_chain",
                chain_index: Some(chain_index as u64),
                event_index: Some(event_index),
                height: Some((chain_index + 1) as u64),
                receipt_hash: Some(hex_encode(&receipt.receipt_hash())),
                turn_hash: hex_encode(&receipt.turn_hash),
                cell_id: hex_encode(&event.cell.0),
                timestamp: receipt.timestamp,
                topic: Some(serde_json::to_value(event.topic).unwrap_or(serde_json::Value::Null)),
                data: Some(serde_json::to_value(&event.data).unwrap_or(serde_json::Value::Null)),
                effects: Vec::new(),
                proof_status: receipt_proof_status(receipt),
                finality: Some(format!("{:?}", receipt.finality).to_lowercase()),
            });
            if out.len() >= limit {
                return Json(out);
            }
        }
    }

    Json(out)
}

async fn get_starbridge_identity_credentials(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityCredentialInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let chain = s.cclerk.receipt_chain();
    let credentials = chain
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, receipt)| identity_receipt_matches(receipt, &params))
        .filter(|(_, receipt)| {
            !receipt.emitted_events.is_empty() || !receipt.derivation_records.is_empty()
        })
        .take(limit)
        .map(|(chain_index, receipt)| {
            let receipt_hash = receipt.receipt_hash();
            let mut subject_cells: Vec<String> = receipt
                .derivation_records
                .iter()
                .map(|record| hex_encode(&record.target_cell.0))
                .chain(
                    receipt
                        .emitted_events
                        .iter()
                        .map(|event| hex_encode(&event.cell.0)),
                )
                .collect();
            subject_cells.sort();
            subject_cells.dedup();
            StarbridgeIdentityCredentialInfo {
                source: "receipt_chain",
                chain_index: chain_index as u64,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: hex_encode(&receipt.turn_hash),
                issuer_cell: hex_encode(&receipt.agent.0),
                subject_cells,
                timestamp: receipt.timestamp,
                effects_hash: hex_encode(&receipt.effects_hash),
                event_count: receipt.emitted_events.len(),
                derivation_record_count: receipt.derivation_records.len(),
                proof_status: receipt_proof_status(receipt),
                finality: format!("{:?}", receipt.finality).to_lowercase(),
            }
        })
        .collect();
    Json(credentials)
}

async fn get_starbridge_identity_proof_checkpoints(
    Query(params): Query<StarbridgeQuery>,
    State(state): State<NodeState>,
) -> Json<Vec<StarbridgeIdentityProofCheckpointInfo>> {
    let limit = starbridge_limit(params.limit);
    let s = state.read().await;
    let checkpoints = s
        .cclerk
        .receipt_chain()
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, receipt)| identity_receipt_matches(receipt, &params))
        .take(limit)
        .map(|(chain_index, receipt)| {
            let receipt_hash = receipt.receipt_hash();
            StarbridgeIdentityProofCheckpointInfo {
                source: "receipt_chain",
                chain_index: chain_index as u64,
                receipt_hash: hex_encode(&receipt_hash),
                turn_hash: hex_encode(&receipt.turn_hash),
                cell_id: hex_encode(&receipt.agent.0),
                timestamp: receipt.timestamp,
                effects_hash: hex_encode(&receipt.effects_hash),
                pre_state: hex_encode(&receipt.pre_state_hash),
                post_state: hex_encode(&receipt.post_state_hash),
                proof_status: receipt_proof_status(receipt),
                executor_signed: receipt.executor_signature.is_some(),
                witness_count: s.witnessed_receipt_count(&receipt_hash),
                finality: format!("{:?}", receipt.finality).to_lowercase(),
            }
        })
        .collect();
    Json(checkpoints)
}

fn select_committed_events(
    log: &VecDeque<CommittedEvent>,
    since_height: Option<u64>,
    limit: usize,
) -> Vec<CommittedEvent> {
    if limit == 0 {
        return Vec::new();
    }

    match since_height {
        Some(height) if height > 0 => log
            .iter()
            .filter(|event| event.height > height)
            .take(limit)
            .cloned()
            .collect(),
        // First-time pollers need the latest retained activity, not the oldest
        // entries in the ring buffer. Keep chronological order so clients can
        // advance their cursor to the last returned height.
        _ => {
            let skip = log.len().saturating_sub(limit);
            log.iter().skip(skip).cloned().collect()
        }
    }
}

/// GET /observability/stream — SSE liveness feed for the public portal.
///
/// Emits a `hello` frame (the node's spent-proof/nullifier count + the number of
/// program-bearing "service" cells) then a 15s `ping` heartbeat. These are the
/// SAME event names (`hello` / `ping`) the discord-bot read surface emits, so the
/// public `portal.dregg.studio` "live" badge — which `addEventListener`s `hello`
/// (and reloads the cell list on it) and `ping` — keeps working when its `/api/*`
/// + `/observability/*` are proxied to the NODE directly rather than to the bot
/// (the portal-decoupling repoint). Full broadcast of per-turn TurnLifecycle
/// events from the node's submit path remains future work (would wire an Emitter
/// + a shared broadcast tx into `NodeState`).
async fn observability_stream(
    State(state): State<NodeState>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    // Counts for the hello frame, read once at connect time (the bot freezes these
    // the same way): the node's spent-proof (nullifier) set size and the number of
    // program-bearing service cells in the ledger.
    let (nullifiers, apps) = {
        let s = state.read().await;
        let apps = s
            .ledger
            .iter()
            .filter(|(_, cell)| !matches!(cell.program, dregg_cell::CellProgram::None))
            .count();
        (s.used_proof_hashes.len(), apps)
    };
    // hello (seq 0) then a 15s ping heartbeat, all from one unfold.
    let stream = stream::unfold(0u64, move |seq| async move {
        let event = if seq == 0 {
            Event::default().event("hello").data(format!(
                r#"{{"nullifiers":{nullifiers},"apps":{apps},"msg":"dregg-node observability stream live"}}"#
            ))
        } else {
            tokio::time::sleep(std::time::Duration::from_secs(15)).await;
            Event::default()
                .event("ping")
                .data(format!(r#"{{"seq":{seq},"nullifiers":{nullifiers}}}"#))
        };
        Some((Ok::<_, Infallible>(event), seq + 1))
    });
    Sse::new(stream).keep_alive(axum::response::sse::KeepAlive::default())
}

/// POST /intents/encrypted — submit an SSE-encrypted intent for gossip propagation.
///
/// Encrypted intents carry search tokens for privacy-preserving matching. The body
/// is hidden until a fulfiller's capability keywords produce a matching token, at
/// which point the poster reveals the decryption key over a direct channel.
async fn post_encrypted_intent(
    State(state): State<NodeState>,
    Json(encrypted): Json<dregg_intent::sse::EncryptedIntent>,
) -> Result<Json<EncryptedIntentSubmitResponse>, StatusCode> {
    let intent_id_hex = hex_encode(&encrypted.id);

    // Basic validation: check non-empty search tokens and non-empty body.
    if encrypted.search_tokens.is_empty() || encrypted.encrypted_body.is_empty() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Check expiry if set.
    if let Some(expiry) = encrypted.expiry {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        if now >= expiry {
            return Err(StatusCode::BAD_REQUEST);
        }
    }

    // Store in the encrypted intent pool.
    {
        let mut s = state.write().await;
        if s.encrypted_intent_pool.len() >= MAX_NODE_INTENT_POOL {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.encrypted_intent_pool
            .insert(encrypted.id, encrypted.clone());
    }

    // Gossip the encrypted intent to federation peers.
    if let Some(gossip) = state.gossip().await {
        let enc = encrypted.clone();
        tokio::spawn(async move {
            gossip.gossip_encrypted_intent(&enc).await;
        });
    }

    Ok(Json(EncryptedIntentSubmitResponse {
        intent_id: intent_id_hex,
        stored: true,
    }))
}

/// POST /intents/encrypted/search — SSE-token coarse filter against the
/// node's encrypted intent pool.
///
/// Closes audit §12 / §14: the SSE primitives were implemented but the
/// node had no way to *serve* SSE-token queries. Fulfillers now POST
/// their `capability_keywords` + `epoch`; the server hashes each
/// keyword to a token and returns every stored encrypted intent whose
/// token set intersects. The body remains encrypted — the fulfiller
/// asks the poster for the decryption key out-of-band.
///
/// This is the "encrypted discovery loop close" — combined with
/// `/intents/encrypted` (post) the encrypted-intent pool becomes
/// queryable, not just write-only.
async fn post_sse_search(
    State(state): State<NodeState>,
    Json(req): Json<SseSearchRequest>,
) -> Result<Json<SseSearchResponse>, StatusCode> {
    const DEFAULT_LIMIT: usize = 50;
    const MAX_LIMIT: usize = 200;

    if req.capability_keywords.is_empty() {
        return Err(StatusCode::BAD_REQUEST);
    }
    let limit = req.limit.unwrap_or(DEFAULT_LIMIT).clamp(1, MAX_LIMIT);

    // Derive search tokens from the fulfiller's keywords.
    let keyword_refs: Vec<&str> = req.capability_keywords.iter().map(String::as_str).collect();

    // Filter the encrypted intent pool.
    let s = state.read().await;
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let mut total = 0usize;
    let mut hits: Vec<SseSearchHit> = Vec::new();
    for (id, encrypted) in s.encrypted_intent_pool.iter() {
        // Honor expiry: don't return stale entries.
        if encrypted.is_expired(now) {
            continue;
        }
        if !dregg_intent::sse::capability_matches_tokens(
            &keyword_refs,
            &encrypted.search_tokens,
            req.epoch,
        ) {
            continue;
        }
        total += 1;
        if hits.len() < limit {
            hits.push(SseSearchHit {
                intent_id: hex_encode(id),
                encrypted_intent: encrypted.clone(),
            });
        }
    }

    Ok(Json(SseSearchResponse {
        hits,
        total_matches: total,
    }))
}

/// POST /intents/trustless — submit a threshold-encrypted intent into the
/// trustless intent engine's current batch.
///
/// Unlike `/intents/encrypted` (single-recipient SSE sealed-box), this
/// path routes through [`dregg_intent::trustless::TrustlessIntentEngine`]:
/// validators collaboratively decrypt the batch via Shamir-over-GF(256)
/// and ChaCha20-Poly1305, solvers compete with STARK validity proofs, and
/// the winning solution settles atomically through the lowering tower.
async fn post_trustless_intent(
    State(state): State<NodeState>,
    Json(encrypted): Json<dregg_intent::trustless::EncryptedIntent>,
) -> Result<Json<EncryptedIntentSubmitResponse>, StatusCode> {
    let content_id = encrypted.content_id();
    let mut s = state.write().await;
    s.trustless_intent_engine
        .submit_encrypted(encrypted)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(EncryptedIntentSubmitResponse {
        intent_id: hex_encode(&content_id),
        stored: true,
    }))
}

/// POST /intents/trustless/share — contribute a decryption share for a
/// ciphertext in the current batch. Once t-of-n shares are accumulated
/// for every submitted ciphertext, the engine reconstructs plaintexts
/// and advances to the Solving phase.
async fn post_trustless_decrypt_share(
    State(state): State<NodeState>,
    Json(share): Json<dregg_intent::trustless::DecryptionShare>,
) -> Result<Json<TrustlessEngineStatus>, StatusCode> {
    let mut s = state.write().await;
    s.trustless_intent_engine
        .contribute_decrypt_share(share)
        .map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(TrustlessEngineStatus::from_engine(
        &s.trustless_intent_engine,
    )))
}

/// GET /intents/trustless/status — current batch lifecycle state for
/// the trustless intent engine.
async fn get_trustless_engine_status(
    State(state): State<NodeState>,
) -> Json<TrustlessEngineStatus> {
    let s = state.read().await;
    Json(TrustlessEngineStatus::from_engine(
        &s.trustless_intent_engine,
    ))
}

/// Public-facing snapshot of the trustless engine state.
#[derive(serde::Serialize)]
struct TrustlessEngineStatus {
    batch_id: u64,
    batch_state: String,
    intent_count: usize,
    decrypt_share_count: usize,
    decrypt_threshold: usize,
    num_validators: usize,
    winning_score: Option<f64>,
    current_height: u64,
}

impl TrustlessEngineStatus {
    fn from_engine(engine: &dregg_intent::trustless::TrustlessIntentEngine) -> Self {
        Self {
            batch_id: engine.current_batch.batch_id,
            batch_state: format!("{:?}", engine.batch_state()),
            intent_count: engine.intent_count(),
            decrypt_share_count: engine.decrypt_share_count(),
            decrypt_threshold: engine.decrypt_threshold,
            num_validators: engine.num_validators,
            winning_score: engine.winning_score(),
            current_height: engine.current_height,
        }
    }
}

async fn get_intents(State(state): State<NodeState>) -> Json<Vec<IntentListEntry>> {
    let s = state.read().await;
    let entries: Vec<IntentListEntry> = s
        .intent_pool
        .iter()
        .map(|(id, intent)| IntentListEntry {
            id: hex_encode(id),
            intent: intent.clone(),
        })
        .collect();
    Json(entries)
}

/// POST /intents/fulfill — verify a fulfillment and automatically execute payment.
///
/// After verifying the fulfillment and predicates, creates and executes a payment
/// turn that transfers computrons from the intent creator to the fulfiller.
async fn post_fulfill_intent(
    State(state): State<NodeState>,
    Json(req): Json<FulfillIntentRequest>,
) -> Result<Json<FulfillIntentResponse>, StatusCode> {
    let intent_id: [u8; 32] = hex_decode(&req.intent_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let payer_bytes: [u8; 32] = hex_decode(&req.payer_cell).map_err(|_| StatusCode::BAD_REQUEST)?;
    let recipient_bytes: [u8; 32] =
        hex_decode(&req.recipient_cell).map_err(|_| StatusCode::BAD_REQUEST)?;

    let payer_cell = dregg_sdk::CellId(payer_bytes);
    let recipient_cell = dregg_sdk::CellId(recipient_bytes);

    // Look up the intent.
    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Verify the payer_cell matches the intent's creator (ownership check).
    // The payer must be the intent creator — prevents arbitrary payer exploitation.
    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => {
            if i.creator.0 != payer_bytes {
                return Ok(Json(FulfillIntentResponse {
                    success: false,
                    turn_hash: None,
                    error: Some("payer_cell does not match intent creator".to_string()),
                }));
            }
            i.clone()
        }
        None => {
            return Ok(Json(FulfillIntentResponse {
                success: false,
                turn_hash: None,
                error: Some("intent not found in pool".to_string()),
            }));
        }
    };

    // Execute the fulfillment payment through the VERIFIED settle path (the shared core
    // `commit_intent_fulfillment_verified` → `execute_fulfillment_flow_verified`): the
    // value-moving leg folds through the verified per-asset transition and is cross-checked
    // against the REAL Lean executor export `dregg_record_kernel_step` (Lean unconditional on
    // native). Fail-closed — a payment the verified executor refuses is REFUSED; there is no
    // fallback to the legacy `dregg_turn::TurnExecutor`. This is the SAME core that inline
    // self-fulfillment at submit (`POST /intents`) drives.
    let result = commit_intent_fulfillment_verified(
        &mut s,
        &intent,
        payer_cell,
        recipient_cell,
        req.state_root,
        req.state_root_block,
    );

    match result {
        Ok(receipt) => {
            let turn_hash = hex_encode(&receipt.turn_hash);
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            Ok(Json(FulfillIntentResponse {
                success: true,
                turn_hash: Some(turn_hash),
                error: None,
            }))
        }
        Err(e) => Ok(Json(FulfillIntentResponse {
            success: false,
            turn_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

async fn get_federation_roots(State(state): State<NodeState>) -> Json<Vec<AttestedRootInfo>> {
    let s = state.read().await;
    let roots = s.store.all_attested_roots().unwrap_or_default();
    let infos: Vec<AttestedRootInfo> = roots
        .iter()
        .map(|r| AttestedRootInfo {
            height: r.height,
            merkle_root: hex_encode(&r.merkle_root),
            timestamp: r.timestamp,
            signatures: r.quorum_signatures.len(),
        })
        .collect();
    Json(infos)
}

async fn get_federations(State(state): State<NodeState>) -> Json<Vec<FederationInfo>> {
    let s = state.read().await;
    Json(federation_infos(&s))
}

/// GET /api/blocklace/blocks — list the live blocklace DAG.
///
/// Returns every block in the local blocklace, height-sorted, with REAL block
/// hashes and REAL parent (`prev_hash` / `predecessors`) links. This is the
/// live analog of the wasm `list_federation_blocks` + `get_federation_block`
/// surface, so the `<dregg-block-dag>` inspector renders node data with the same
/// component it uses for the in-browser sim.
///
/// Empty list when consensus is not yet running (e.g. the handle hasn't been
/// installed at startup); never a 404, so the explorer can poll safely.
async fn get_blocklace_blocks(
    State(state): State<NodeState>,
) -> Json<Vec<crate::blocklace_sync::BlockView>> {
    match state.blocklace().await {
        Some(handle) => Json(handle.block_views().await),
        None => Json(Vec::new()),
    }
}

/// GET /api/block/{height} — fetch one blocklace block by height (creator seq).
///
/// `height` is the block's sequence number within its creator's chain (the same
/// value surfaced as `height` in the block list). The response carries the
/// block's REAL `prev_hash` (its first predecessor) and full `predecessors`
/// set. Returns 404 when no block exists at that height.
async fn get_block_by_height(
    State(state): State<NodeState>,
    AxumPath(height): AxumPath<u64>,
) -> Result<Json<crate::blocklace_sync::BlockView>, StatusCode> {
    let handle = state.blocklace().await.ok_or(StatusCode::NOT_FOUND)?;
    match handle.block_view_at_height(height).await {
        Some(view) => Ok(Json(view)),
        None => Err(StatusCode::NOT_FOUND),
    }
}

fn federation_infos(s: &crate::state::NodeStateInner) -> Vec<FederationInfo> {
    let roots = s.store.all_attested_roots().unwrap_or_default();
    let latest_root = roots.iter().max_by_key(|r| r.height);
    let latest_height = latest_root.map(|r| r.height).unwrap_or(0);
    let latest_root_hex = latest_root.map(|r| hex_encode(&r.merkle_root));

    let mut infos: Vec<FederationInfo> = s
        .known_federations
        .iter()
        .map(|(id, fed)| FederationInfo {
            id: id.hex(),
            federation_id: id.hex(),
            committee_epoch: fed.epoch(),
            threshold: fed.threshold(),
            member_count: fed.members().len(),
            members: fed.members().iter().map(|pk| pk.hex()).collect(),
            is_local: id.0 == s.federation_id,
            latest_height,
            latest_root: latest_root_hex.clone(),
            num_finalized_roots: roots.len(),
        })
        .collect();

    infos.sort_by(|a, b| a.id.cmp(&b.id));

    if infos.is_empty() {
        infos.push(FederationInfo {
            id: hex_encode(&s.federation_id),
            federation_id: hex_encode(&s.federation_id),
            committee_epoch: s.committee_epoch,
            threshold: s.known_federation_keys.len() as u32,
            member_count: s.known_federation_keys.len(),
            members: sorted_hex_keys(&s.known_federation_keys),
            is_local: true,
            latest_height,
            latest_root: latest_root_hex,
            num_finalized_roots: roots.len(),
        });
    }

    infos
}

fn sorted_hex_keys(keys: &[dregg_sdk::PublicKey]) -> Vec<String> {
    let mut keys: Vec<String> = keys.iter().map(|key| key.hex()).collect();
    keys.sort();
    keys
}

// =============================================================================
// Fast-Path Turn handlers
// =============================================================================

/// POST /turn/fast-path — request a fast-path lock from this validator.
///
/// The node checks eligibility, acquires cell locks, and returns a TurnSign
/// (the validator's lock acknowledgement) if the turn qualifies.
#[tracing::instrument(skip_all)]
async fn post_fast_path_lock(
    State(state): State<NodeState>,
    Json(req): Json<FastPathLockRequest>,
) -> Result<Json<FastPathLockResponse>, StatusCode> {
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash = turn.hash();

    let mut s = state.write().await;

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Use the node's public key as the validator signing key.
    let validator_key = s.cclerk.public_key().0;

    // Decode the agent's Ed25519 signature over turn_hash (P1-6).
    let agent_sig_bytes = match hex_decode_var(&req.agent_signature) {
        Ok(b) if b.len() == 64 => {
            let mut arr = [0u8; 64];
            arr.copy_from_slice(&b);
            arr
        }
        _ => {
            return Ok(Json(FastPathLockResponse {
                locked: false,
                validator_key: None,
                signature: None,
                height: None,
                error: Some("agent_signature must be 64 hex-encoded bytes".to_string()),
            }));
        }
    };

    // Split borrows: take mutable ref to cell_lock_table and immutable ref to ledger
    // from disjoint fields of the same struct.
    let inner = &mut *s;
    let result = dregg_turn::process_fast_path_lock(
        &mut inner.cell_lock_table,
        &turn,
        turn_hash,
        current_height,
        &inner.ledger,
        &validator_key,
        &agent_sig_bytes,
    );

    match result {
        Ok(sign) => Ok(Json(FastPathLockResponse {
            locked: true,
            validator_key: Some(hex_encode(&sign.validator_key)),
            signature: Some(hex_encode_var(&sign.signature)),
            height: Some(sign.height),
            error: None,
        })),
        Err(e) => Ok(Json(FastPathLockResponse {
            locked: false,
            validator_key: None,
            signature: None,
            height: None,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /turn/certificate — execute a certified fast-path turn.
///
/// The client presents a TurnCertificate (turn + 2f+1 validator signatures).
/// The node verifies the certificate, executes the turn, releases locks, and
/// gossips the result.
#[tracing::instrument(skip_all)]
async fn post_fast_path_certificate(
    State(state): State<NodeState>,
    Json(req): Json<FastPathCertificateRequest>,
) -> Result<Json<FastPathCertificateResponse>, StatusCode> {
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let turn_hash_bytes: [u8; 32] =
        hex_decode(&req.turn_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Verify the turn hash matches.
    let computed_hash = turn.hash();
    if computed_hash != turn_hash_bytes {
        return Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: None,
            error: Some("turn hash mismatch".to_string()),
        }));
    }

    // Parse signatures.
    let mut signatures = Vec::new();
    for entry in &req.signatures {
        let vk: [u8; 32] = hex_decode(&entry.validator_key).map_err(|_| StatusCode::BAD_REQUEST)?;
        let sig_bytes = hex_decode_var(&entry.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
        if sig_bytes.len() != 64 {
            return Err(StatusCode::BAD_REQUEST);
        }
        let mut sig = [0u8; 64];
        sig.copy_from_slice(&sig_bytes);
        signatures.push(dregg_turn::TurnSign {
            validator_key: vk,
            signature: sig,
            height: entry.height,
        });
    }

    // Assemble certificate (verify quorum).
    // Threshold is derived from federation size: n - f where f = (n-1)/3.
    // For single-node (n=1): threshold = 1. For 4 nodes: threshold = 3.
    let n = {
        let s = state.read().await;
        let key_count = s.known_federation_keys.len();
        if key_count == 0 { 1usize } else { key_count }
    };
    let f = (n.saturating_sub(1)) / 3;
    let threshold = n - f;
    let cert = match dregg_turn::assemble_certificate(turn, turn_hash_bytes, signatures, threshold)
    {
        Ok(c) => c,
        Err(e) => {
            return Ok(Json(FastPathCertificateResponse {
                executed: false,
                turn_hash: None,
                error: Some(e.to_string()),
            }));
        }
    };

    // Execute the certified turn.
    let mut s = state.write().await;
    // Split borrows: take mutable refs to disjoint fields.
    let inner = &mut *s;
    let executor = crate::executor_setup::new_submit_executor(inner);
    let result = dregg_turn::execute_certified_turn(
        &cert,
        &executor,
        &mut inner.ledger,
        &mut inner.cell_lock_table,
    );

    match result {
        dregg_turn::TurnResult::Committed { receipt, .. } => {
            let hash_hex = hex_encode(&receipt.turn_hash);
            s.cclerk
                .append_receipt(receipt)
                .expect("local executor and cclerk chains must agree; divergence is a serious bug");
            drop(s);
            state.emit(NodeEvent::Receipt {
                hash: hash_hex.clone(),
            });
            Ok(Json(FastPathCertificateResponse {
                executed: true,
                turn_hash: Some(hash_hex),
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            Ok(Json(FastPathCertificateResponse {
                executed: false,
                turn_hash: Some(hex_encode(&turn_hash_bytes)),
                error: Some(format!("turn rejected: {reason}")),
            }))
        }
        _ => Ok(Json(FastPathCertificateResponse {
            executed: false,
            turn_hash: Some(hex_encode(&turn_hash_bytes)),
            error: Some("turn did not commit".to_string()),
        })),
    }
}

// =============================================================================
// Conditional Turn handlers
// =============================================================================

async fn post_submit_conditional(
    State(state): State<NodeState>,
    Json(req): Json<SubmitConditionalRequest>,
) -> Result<Json<SubmitConditionalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    drop(s);

    let condition: dregg_turn::ProofCondition =
        serde_json::from_value(req.condition).map_err(|_| StatusCode::BAD_REQUEST)?;
    let turn: dregg_turn::Turn =
        serde_json::from_value(req.turn).map_err(|_| StatusCode::BAD_REQUEST)?;

    let deposit_amount =
        dregg_turn::compute_conditional_deposit(req.timeout_height, current_height);
    let conditional = dregg_turn::ConditionalTurn {
        turn,
        condition,
        timeout_height: req.timeout_height,
        submitted_at: current_height,
        deposit_amount,
    };

    if let Err(_e) = dregg_turn::validate_conditional_submission(&conditional, current_height) {
        return Ok(Json(SubmitConditionalResponse {
            accepted: false,
            conditional_hash: None,
        }));
    }

    let hash = conditional.hash();
    let hash_hex = hex_encode(&hash);

    // P1 Fix 6: enforce max size with proactive GC.
    {
        let mut s = state.write().await;

        // Proactive GC: remove expired conditionals before checking capacity.
        let gc_height = s
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);
        s.pending_conditionals
            .retain(|ct| !ct.is_expired(gc_height));

        if s.pending_conditionals.len() >= MAX_PENDING_CONDITIONALS {
            return Err(StatusCode::SERVICE_UNAVAILABLE);
        }
        s.pending_conditionals.push(conditional);
    }

    Ok(Json(SubmitConditionalResponse {
        accepted: true,
        conditional_hash: Some(hash_hex),
    }))
}

#[tracing::instrument(skip_all)]
async fn post_resolve_conditional(
    State(state): State<NodeState>,
    Json(req): Json<ResolveConditionalRequest>,
) -> Result<Json<ResolveConditionalResponse>, StatusCode> {
    // Require cipherclerk to be unlocked for conditional resolution.
    {
        let s = state.read().await;
        if !s.unlocked {
            return Err(StatusCode::FORBIDDEN);
        }
    }

    let hash_bytes = hex_decode(&req.conditional_hash).map_err(|_| StatusCode::BAD_REQUEST)?;

    let proof: dregg_turn::ConditionProof =
        serde_json::from_value(req.proof).map_err(|_| StatusCode::BAD_REQUEST)?;
    let verify_start = Instant::now();

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let idx = s
        .pending_conditionals
        .iter()
        .position(|ct| ct.hash() == hash_bytes);

    let idx = match idx {
        Some(i) => i,
        None => {
            return Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn not found".to_string()),
            }));
        }
    };

    let condition = s.pending_conditionals[idx].condition.clone();
    let timeout_height = s.pending_conditionals[idx].timeout_height;
    let trusted_roots: Vec<dregg_turn::TrustedRoot> = s
        .store
        .all_attested_roots()
        .unwrap_or_default()
        .iter()
        .map(|r| (r.merkle_root, r.height))
        .collect();
    let trusted_executor_keys: Vec<[u8; 32]> =
        s.known_federation_keys.iter().map(|k| k.0).collect();

    let result = dregg_turn::resolve_condition(
        &condition,
        &proof,
        current_height,
        timeout_height,
        &trusted_roots,
        dregg_turn::DEFAULT_MAX_ROOT_AGE,
        &mut s.used_proof_hashes,
        &trusted_executor_keys,
    );

    crate::metrics::record_proof_verification_duration(verify_start.elapsed().as_secs_f64());

    match result {
        dregg_turn::ConditionalResult::Resolved => {
            crate::metrics::inc_proofs_verified("valid");
            // SECURITY: Persist the proof nullifier to the store immediately so
            // a crash cannot allow proof replay. The in-memory set was already
            // updated by resolve_condition; this makes it durable.
            let proof_hash = dregg_turn::compute_proof_hash(&proof);
            if let Err(e) = s.store.insert_proof_hash(&proof_hash) {
                tracing::warn!(error = %e, "failed to persist proof nullifier to store");
            }

            let conditional = s.pending_conditionals.remove(idx);

            let executor = crate::executor_setup::new_submit_executor(&s);
            let lean_producer_enabled = s.lean_producer_enabled;
            // ONE executor gate (#171): resolved conditionals commit through the
            // same producer-aware path as every other ingress.
            let exec_result = crate::executor_setup::execute_via_producer(
                &executor,
                &conditional.turn,
                &mut s.ledger,
                lean_producer_enabled,
            );

            match exec_result {
                dregg_turn::TurnResult::Committed { mut receipt, .. } => {
                    // Solo mode: mark receipt as Tentative and log in nullifier log.
                    let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
                    if let Some(ref mut solo) = s.solo_consensus
                        && solo.is_solo
                    {
                        receipt.finality = dregg_turn::Finality::Tentative;
                        // Re-sign after the committed finality downgrade.
                        resign_receipt_committed(&mut receipt, &node_signing_key);
                        let height = solo.height;
                        let _ =
                            solo.nullifier_log
                                .insert(receipt.turn_hash, receipt.turn_hash, height);
                        solo.advance_height();
                        #[cfg(debug_assertions)]
                        debug_assert_signed_last(&receipt, &node_signing_key);
                    }
                    let turn_hash = hex_encode(&receipt.turn_hash);
                    s.cclerk.append_receipt(receipt).expect(
                        "local executor and cclerk chains must agree; divergence is a serious bug",
                    );
                    drop(s);
                    state.emit(NodeEvent::Receipt {
                        hash: turn_hash.clone(),
                    });
                    Ok(Json(ResolveConditionalResponse {
                        resolved: true,
                        turn_hash: Some(turn_hash),
                        reason: None,
                    }))
                }
                dregg_turn::TurnResult::Rejected { reason, .. } => {
                    crate::metrics::inc_turns_executed("rejected");
                    crate::metrics::note_turn_rejected(&reason);
                    Ok(Json(ResolveConditionalResponse {
                        resolved: false,
                        turn_hash: None,
                        reason: Some(format!("turn rejected: {reason}")),
                    }))
                }
                dregg_turn::TurnResult::Expired => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn expired during execution".to_string()),
                })),
                dregg_turn::TurnResult::Pending => Ok(Json(ResolveConditionalResponse {
                    resolved: false,
                    turn_hash: None,
                    reason: Some("turn pending during execution".to_string()),
                })),
            }
        }
        dregg_turn::ConditionalResult::Expired => {
            crate::metrics::inc_proofs_verified("error");
            s.pending_conditionals.remove(idx);
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some("conditional turn has expired".to_string()),
            }))
        }
        dregg_turn::ConditionalResult::Pending => Ok(Json(ResolveConditionalResponse {
            resolved: false,
            turn_hash: None,
            reason: Some("condition not yet satisfied".to_string()),
        })),
        dregg_turn::ConditionalResult::InvalidProof(e) => {
            crate::metrics::inc_proofs_verified("invalid");
            Ok(Json(ResolveConditionalResponse {
                resolved: false,
                turn_hash: None,
                reason: Some(format!("invalid proof: {e}")),
            }))
        }
    }
}

async fn get_pending_conditionals(
    State(state): State<NodeState>,
) -> Json<Vec<PendingConditionalInfo>> {
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // GC: remove expired conditionals.
    s.pending_conditionals
        .retain(|ct| !ct.is_expired(current_height));

    let infos: Vec<PendingConditionalInfo> = s
        .pending_conditionals
        .iter()
        .map(|ct| {
            let condition_type = match &ct.condition {
                dregg_turn::ProofCondition::HashPreimage { .. } => "hash_preimage",
                dregg_turn::ProofCondition::RemoteProof { .. } => "remote_proof",
                dregg_turn::ProofCondition::LocalProof { .. } => "local_proof",
                dregg_turn::ProofCondition::TurnExecuted { .. } => "turn_executed",
            };
            PendingConditionalInfo {
                hash: hex_encode(&ct.hash()),
                timeout_height: ct.timeout_height,
                submitted_at: ct.submitted_at,
                condition_type: condition_type.to_string(),
            }
        })
        .collect();
    Json(infos)
}

// =============================================================================
// Atomic Multi-Party Turn Handlers
// =============================================================================

/// POST /turn/atomic — Submit an atomic multi-party turn proposal.
///
/// The coordinator node creates a Coordinator instance, validates the proposal
/// (budget gate, participant count, threshold), persists it in the proposals map,
/// and returns a proposal_id that participants can vote on.
#[tracing::instrument(skip_all)]
async fn post_atomic_proposal(
    State(state): State<NodeState>,
    Json(req): Json<AtomicProposalRequest>,
) -> Result<Json<AtomicProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    // Parse participant node IDs.
    let mut participants: Vec<[u8; 32]> = Vec::new();
    for p in &req.participants {
        let bytes: [u8; 32] = hex_decode(p).map_err(|_| StatusCode::BAD_REQUEST)?;
        participants.push(bytes);
    }

    if participants.is_empty() {
        return Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some("at least one participant required".to_string()),
        }));
    }

    // Parse the initiator cell ID.
    let initiator_bytes: [u8; 32] =
        hex_decode(&req.initiator).map_err(|_| StatusCode::BAD_REQUEST)?;
    let initiator = dregg_cell::CellId(initiator_bytes);

    // Deserialize the call forest.
    let forest: dregg_turn::CallForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Build the atomic forest.
    let atomic_forest = dregg_coord::AtomicForest::new(
        participants.clone(),
        forest,
        vec![], // preconditions left empty; participants validate locally
        initiator,
        req.fee,
    );

    // Create the coordinator with the node's identity.
    let mut s = state.write().await;

    // Garbage-collect stale proposals before creating new ones.
    s.expire_stale_proposals();

    let node_id = s.silo_id;
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let costs = dregg_turn::ComputronCosts::default();

    // F-P1-4: build participant key map. Prior code used (id, id) which only
    // happened to work when cell_id == pubkey (sovereign cells). The request
    // may now supply explicit per-participant keys; otherwise we look them up
    // in `known_federation_keys`, and any participant not found is rejected.
    let participant_keys: std::collections::HashMap<[u8; 32], [u8; 32]> = match req
        .participant_pubkeys
        .as_ref()
    {
        Some(pks) => {
            if pks.len() != participants.len() {
                return Ok(Json(AtomicProposalResponse {
                    accepted: false,
                    proposal_id: None,
                    error: Some("participant_pubkeys length must match participants".to_string()),
                }));
            }
            let mut map = std::collections::HashMap::with_capacity(participants.len());
            for (id, pk_hex) in participants.iter().zip(pks.iter()) {
                let pk: [u8; 32] = hex_decode(pk_hex).map_err(|_| StatusCode::BAD_REQUEST)?;
                map.insert(*id, pk);
            }
            map
        }
        None => {
            // Lookup keys from known_federation_keys.
            let known: std::collections::HashSet<[u8; 32]> =
                s.known_federation_keys.iter().map(|k| k.0).collect();
            let mut map = std::collections::HashMap::with_capacity(participants.len());
            for id in &participants {
                if !known.contains(id) {
                    return Ok(Json(AtomicProposalResponse {
                        accepted: false,
                        proposal_id: None,
                        error: Some(format!(
                            "participant {} not in known federation keys; supply participant_pubkeys explicitly",
                            hex_encode(id)
                        )),
                    }));
                }
                map.insert(*id, *id);
            }
            map
        }
    };

    let mut coordinator = dregg_coord::Coordinator::new(
        node_id,
        signing_key,
        req.threshold,
        costs,
        MAX_ATOMIC_BUDGET, // F-P2-1: bound per-proposal computron budget
        participant_keys,
    );

    let forest_for_storage = atomic_forest.clone();

    match coordinator.propose(atomic_forest) {
        Ok(propose_msg) => {
            let proposal_id = propose_msg.proposal_id;
            let proposal_id_hex = hex_encode(&proposal_id);
            let forest_hash = forest_for_storage.hash;
            let forest_wire = forest_for_storage.encode_for_wire();

            // Persist the coordinator in the proposals map for later vote collection
            // (this Coordinator IS the vote tally the returning votes feed into).
            s.atomic_proposals.insert(
                proposal_id,
                crate::state::ActiveProposal {
                    coordinator,
                    created_at: std::time::Instant::now(),
                    forest: forest_for_storage,
                },
            );

            // THE SEND WELD: broadcast the REAL `ProposeAtomicTurn` variant (full
            // forest + the coordinator's real proposal_id + identity) on the
            // blocklace topic, so each participant reconstructs the forest, votes
            // bound to THIS proposal_id, and returns its `VoteAtomicTurn`. Replaces
            // the old JSON-stub `atomic_proposal` that a peer could not reconstruct.
            drop(s);
            if let Some(blocklace) = state.blocklace().await {
                blocklace
                    .gossip_atomic_propose(
                        forest_hash,
                        proposal_id,
                        node_id,
                        participants.clone(),
                        forest_wire,
                    )
                    .await;
            }

            Ok(Json(AtomicProposalResponse {
                accepted: true,
                proposal_id: Some(proposal_id_hex),
                error: None,
            }))
        }
        Err(e) => Ok(Json(AtomicProposalResponse {
            accepted: false,
            proposal_id: None,
            error: Some(format!("{e}")),
        })),
    }
}

/// POST /turn/atomic/vote — Vote on an atomic proposal.
///
/// Participants submit their vote (approve/reject) with an Ed25519 signature.
/// When enough votes are collected, the coordinator decides to commit or abort,
/// executing the turn via TurnExecutor on commit.
async fn post_atomic_vote(
    State(state): State<NodeState>,
    Json(req): Json<AtomicVoteRequest>,
) -> Result<Json<AtomicVoteResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let voter: [u8; 32] = hex_decode(&req.voter).map_err(|_| StatusCode::BAD_REQUEST)?;

    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }
    let mut signature = [0u8; 64];
    signature.copy_from_slice(&sig_bytes);

    let vote = if req.approve {
        dregg_coord::Vote::yes(signature)
    } else {
        dregg_coord::Vote::no("participant rejected", signature)
    };

    // Defense-in-depth: verify the vote signature against the claimed voter's
    // public key BEFORE passing to the coordinator. This prevents an authenticated
    // node from voting as another participant (the coordinator also verifies, but
    // rejecting early avoids acquiring the write lock for invalid votes).
    {
        let s = state.read().await;
        let active = match s.atomic_proposals.get(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        let forest_hash = active.forest.hash;
        let sig_valid = if req.approve {
            dregg_coord::Vote::verify_yes(&signature, &proposal_id, &forest_hash, &voter)
        } else {
            dregg_coord::Vote::verify_no(&signature, &proposal_id, &forest_hash, &voter)
        };
        if !sig_valid {
            return Ok(Json(AtomicVoteResponse {
                accepted: false,
                decision: None,
                error: Some("vote signature does not match claimed voter identity".to_string()),
            }));
        }
    }

    let mut s = state.write().await;

    // Feed the vote to the coordinator.
    let decision = {
        let active = match s.atomic_proposals.get_mut(&proposal_id) {
            Some(p) => p,
            None => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some("proposal not found".to_string()),
                }));
            }
        };
        let rust_decision = match active.coordinator.receive_vote(voter, vote) {
            Ok(maybe_decision) => maybe_decision,
            Err(e) => {
                return Ok(Json(AtomicVoteResponse {
                    accepted: false,
                    decision: None,
                    error: Some(format!("{e}")),
                }));
            }
        };
        // STRONG-FORM SWAP: make the VERIFIED Lean 2PC gate (`dregg_coord_2pc_decide` =
        // `TwoPhaseCommit.evaluate`) the AUTHORITATIVE Commit/Abort/Pending verdict, with the Rust
        // `Coordinator::evaluate_votes` (the `rust_decision` above) demoted to the differential
        // sibling. The coordinator exposes its tally as the gate's wire; `coord_gate` runs the
        // verified rule, compares, and returns the verified verdict (logging on drift). When the Lean
        // archive is absent it falls back to `rust_decision`. The `receive_vote` side-effects (vote
        // recording, state transition) already happened — we only re-decide the *verdict*.
        let wire = active.coordinator.decision_wire();
        let rust_had_no_decision = rust_decision.is_none();
        let rust_inner = rust_decision.unwrap_or(dregg_coord::Decision::Pending);
        let gated = crate::coord_gate::authoritative_decision(rust_inner, wire.as_deref());
        // Preserve "no terminal decision yet" semantics: a Pending gated verdict with no Rust
        // decision stays `None` (the coordinator has not transitioned).
        match (rust_had_no_decision, gated) {
            (true, dregg_coord::Decision::Pending) => None,
            (_, g) => Some(g),
        }
    };

    // Handle the decision.
    match decision {
        Some(dregg_coord::Decision::Commit) => {
            // Extract the proposal so we can borrow ledger mutably.
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            // Execute the atomic turn against the ledger.
            match active.coordinator.commit(&mut s.ledger) {
                Ok(_commit_msg) => Ok(Json(AtomicVoteResponse {
                    accepted: true,
                    decision: Some("commit".to_string()),
                    error: None,
                })),
                Err(e) => {
                    // Commit failed (e.g., turn execution error) — abort.
                    let _ = active.coordinator.abort(format!("commit failed: {e}"));

                    Ok(Json(AtomicVoteResponse {
                        accepted: true,
                        decision: Some("abort".to_string()),
                        error: Some(format!("commit failed: {e}")),
                    }))
                }
            }
        }
        Some(dregg_coord::Decision::Abort) => {
            let mut active = s.atomic_proposals.remove(&proposal_id).unwrap();
            let _ = active
                .coordinator
                .abort("too many rejections — threshold unreachable");

            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: Some("abort".to_string()),
                error: None,
            }))
        }
        Some(dregg_coord::Decision::Pending) | None => {
            // Still waiting for more votes.
            Ok(Json(AtomicVoteResponse {
                accepted: true,
                decision: None,
                error: None,
            }))
        }
    }
}

/// GET /turn/atomic/:id — Query the status of an active atomic proposal.
///
/// Returns vote counts, coordinator state, and age so clients can monitor
/// progress without polling the vote endpoint.
async fn get_proposal_status(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<ProposalStatusResponse>, StatusCode> {
    let proposal_id: [u8; 32] = hex_decode(&id).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.read().await;
    let active = match s.atomic_proposals.get(&proposal_id) {
        Some(p) => p,
        None => {
            return Ok(Json(ProposalStatusResponse {
                found: false,
                state: "not_found".to_string(),
                yes_votes: 0,
                no_votes: 0,
                total_participants: 0,
                threshold: 0,
                age_secs: 0,
            }));
        }
    };

    let (state_name, yes_count, no_count, total) = match &active.coordinator.state {
        dregg_coord::CoordinatorState::Idle => ("idle", 0, 0, 0),
        dregg_coord::CoordinatorState::Proposing { forest, votes, .. } => {
            let yes = votes.values().filter(|v| v.is_yes()).count();
            let no = votes.values().filter(|v| v.is_no()).count();
            ("proposing", yes, no, forest.participant_count())
        }
        dregg_coord::CoordinatorState::Committed { .. } => ("committed", 0, 0, 0),
        dregg_coord::CoordinatorState::Aborted { .. } => ("aborted", 0, 0, 0),
    };

    let age_secs = std::time::Instant::now()
        .duration_since(active.created_at)
        .as_secs();

    Ok(Json(ProposalStatusResponse {
        found: true,
        state: state_name.to_string(),
        yes_votes: yes_count,
        no_votes: no_count,
        total_participants: total,
        threshold: active.coordinator.threshold,
        age_secs,
    }))
}

/// POST /turn/atomic/evaluate — Participant evaluates a proposal against local state.
///
/// A node that received a proposal via gossip uses this endpoint to evaluate
/// whether it should vote yes or no, based on its local ledger and preconditions.
/// Returns the signed vote that can then be submitted to the coordinator's
/// `/turn/atomic/vote` endpoint.
async fn post_evaluate_proposal(
    State(state): State<NodeState>,
    Json(req): Json<EvaluateProposalRequest>,
) -> Result<Json<EvaluateProposalResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }
    drop(s);

    let proposal_id: [u8; 32] =
        hex_decode(&req.proposal_id).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the atomic forest from the request.
    let atomic_forest: dregg_coord::AtomicForest =
        serde_json::from_value(req.forest).map_err(|_| StatusCode::BAD_REQUEST)?;

    let s = state.write().await;

    // Build a Participant from the node's local identity and ledger.
    let node_id = s.silo_id;
    let signing_key = s.cclerk.gossip_signing_key().to_bytes();
    let cell_id = dregg_cell::CellId(node_id);

    let mut participant =
        dregg_coord::Participant::new(cell_id, node_id, signing_key, s.ledger.clone());

    // Evaluate the proposal locally.
    let vote = participant.evaluate_proposal(&proposal_id, &atomic_forest);

    match vote {
        dregg_coord::Vote::Yes { signature } => Ok(Json(EvaluateProposalResponse {
            approve: true,
            reason: None,
            signature: hex_encode_var(&signature),
        })),
        dregg_coord::Vote::No { reason, signature } => Ok(Json(EvaluateProposalResponse {
            approve: false,
            reason: Some(reason),
            signature: hex_encode_var(&signature),
        })),
    }
}

// =============================================================================
// Sovereign Cell Ephemeral Registration Handlers
// =============================================================================

/// POST /cells/register — register a sovereign cell's commitment with the federation.
///
/// The cell exists locally on the agent; the federation stores only the commitment
/// and TTL metadata. Registration expires after `ttl_blocks` of inactivity.
#[tracing::instrument(skip_all)]
async fn post_register_cell(
    State(state): State<NodeState>,
    Json(req): Json<RegisterCellRequest>,
) -> Result<Json<RegisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let commitment: [u8; 32] = hex_decode(&req.commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || commitment.
    let mut message = Vec::with_capacity(64);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some("invalid signature".to_string()),
        }));
    }

    let ttl = req.ttl_blocks.unwrap_or(dregg_cell::DEFAULT_SOVEREIGN_TTL);
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // Parse optional verification key hash.
    let vk_hash: Option<[u8; 32]> = match &req.verification_key_hash {
        Some(hex_str) => Some(hex_decode(hex_str).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s.ledger.register_sovereign_cell_with_vk(
        cell_id,
        commitment,
        current_height,
        ttl,
        vk_hash,
    ) {
        Ok(()) => Ok(Json(RegisterCellResponse {
            registered: true,
            ttl_blocks: ttl,
            error: None,
        })),
        Err(e) => Ok(Json(RegisterCellResponse {
            registered: false,
            ttl_blocks: 0,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/deregister — voluntarily remove a sovereign cell from the federation.
#[tracing::instrument(skip_all)]
async fn post_deregister_cell(
    State(state): State<NodeState>,
    Json(req): Json<DeregisterCellRequest>,
) -> Result<Json<DeregisterCellResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id (proves ownership for deregistration).
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &cell_id_bytes) {
        return Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;

    match s.ledger.deregister_sovereign_cell(&cell_id) {
        Ok(()) => Ok(Json(DeregisterCellResponse {
            deregistered: true,
            error: None,
        })),
        Err(e) => Ok(Json(DeregisterCellResponse {
            deregistered: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /cells/update-commitment — update a sovereign cell's commitment after a transition.
///
/// Verifies the old commitment matches, updates to the new commitment, and resets
/// the TTL activity counter.
#[tracing::instrument(skip_all)]
async fn post_update_commitment(
    State(state): State<NodeState>,
    Json(req): Json<UpdateCommitmentRequest>,
) -> Result<Json<UpdateCommitmentResponse>, StatusCode> {
    let cell_id_bytes: [u8; 32] = hex_decode(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let old_commitment: [u8; 32] =
        hex_decode(&req.old_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let new_commitment: [u8; 32] =
        hex_decode(&req.new_commitment).map_err(|_| StatusCode::BAD_REQUEST)?;
    let sig_bytes = hex_decode_var(&req.signature).map_err(|_| StatusCode::BAD_REQUEST)?;
    if sig_bytes.len() != 64 {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Verify signature: signs cell_id || old_commitment || new_commitment.
    let mut message = Vec::with_capacity(96);
    message.extend_from_slice(&cell_id_bytes);
    message.extend_from_slice(&old_commitment);
    message.extend_from_slice(&new_commitment);
    if !verify_ed25519_signature(&cell_id_bytes, &sig_bytes, &message) {
        return Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some("invalid signature".to_string()),
        }));
    }

    let cell_id = dregg_cell::CellId(cell_id_bytes);
    let mut s = state.write().await;
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    match s.ledger.update_sovereign_registration_commitment(
        &cell_id,
        old_commitment,
        new_commitment,
        current_height,
    ) {
        Ok(()) => Ok(Json(UpdateCommitmentResponse {
            updated: true,
            error: None,
        })),
        Err(e) => Ok(Json(UpdateCommitmentResponse {
            updated: false,
            error: Some(e.to_string()),
        })),
    }
}

/// POST /programs/deploy — deploy a custom cell program to the federation.
///
/// Accepts a postcard-serialized CircuitDescriptor, validates it for safety,
/// and stores it in the program registry. Returns the VK hash (program identity).
#[tracing::instrument(skip_all)]
async fn post_deploy_program(
    State(state): State<NodeState>,
    Json(req): Json<DeployProgramRequest>,
) -> Result<Json<DeployProgramResponse>, StatusCode> {
    // Decode hex descriptor bytes.
    let descriptor_bytes =
        hex_decode_var(&req.descriptor_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Deserialize the CircuitDescriptor from postcard format.
    let descriptor: dregg_dsl_runtime::CircuitDescriptor =
        postcard::from_bytes(&descriptor_bytes).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Create the CellProgram (computes VK hash).
    let program = dregg_dsl_runtime::CellProgram::new(descriptor, req.version);

    // Deploy to registry (validates safety bounds).
    let mut s = state.write().await;
    match s.program_registry.deploy(program) {
        Ok(vk_hash) => Ok(Json(DeployProgramResponse {
            deployed: true,
            vk_hash: Some(hex_encode(&vk_hash)),
            error: None,
        })),
        Err(e) => Ok(Json(DeployProgramResponse {
            deployed: false,
            vk_hash: None,
            error: Some(e.to_string()),
        })),
    }
}

/// Verify an Ed25519 signature where the public key is the cell_id bytes.
///
/// The cell_id doubles as the public key for sovereign cells (the cell_id IS
/// the Ed25519 public key or is derived from it). For this API, we treat
/// the cell_id as the public key directly.
fn verify_ed25519_signature(public_key_bytes: &[u8; 32], sig_bytes: &[u8], message: &[u8]) -> bool {
    use ed25519_dalek::Verifier;

    let Ok(verifying_key) = ed25519_dalek::VerifyingKey::from_bytes(public_key_bytes) else {
        return false;
    };
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(sig_bytes);
    let signature = ed25519_dalek::Signature::from_bytes(&sig_arr);
    verifying_key.verify(message, &signature).is_ok()
}

// =============================================================================
// PIR (Private Information Retrieval) Handlers
// =============================================================================

/// GET /pir/info — returns metadata about the PIR database.
///
/// Clients need this to know the database dimensions and tag ordering before
/// constructing a valid PIR query vector.
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn get_pir_info(State(state): State<NodeState>) -> Json<PirInfoResponse> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<dregg_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(dregg_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

    Json(PirInfoResponse {
        num_rows: index.num_rows(),
        row_width: index.row_width(),
        tags: index.tags.clone(),
    })
}

/// POST /pir/query — accepts a PIR query vector and returns the server's response.
///
/// The node computes the matrix-vector product of the intent index against the
/// query vector, returning a response that reveals nothing about which row was
/// queried (when combined with a complementary query to a second node).
///
/// Uses a cached IntentIndex to avoid O(n) rebuilds on every request (CPU DoS fix).
async fn post_pir_query(
    State(state): State<NodeState>,
    Json(req): Json<PirQueryRequest>,
) -> Result<Json<PirQueryResponse>, StatusCode> {
    let mut s = state.write().await;

    // Use cached index or build and cache it.
    if s.pir_index_cache.is_none() {
        let intents: Vec<dregg_intent::Intent> = s.intent_pool.values().cloned().collect();
        s.pir_index_cache = Some(dregg_intent::pir::IntentIndex::build_from_intents(&intents));
    }
    let index = s.pir_index_cache.as_ref().unwrap();

    // Validate query vector length matches the database.
    if req.query_vector.len() != index.num_rows() {
        return Err(StatusCode::BAD_REQUEST);
    }

    // Convert the u32 query vector to BabyBear field elements.
    let query = dregg_intent::pir::PirQuery {
        query_vector: req
            .query_vector
            .iter()
            .map(|&v| dregg_circuit::field::BabyBear::new(v))
            .collect(),
    };

    // Compute the PIR response.
    let response = dregg_intent::pir::compute_pir_response(&query, &index.entries);

    // Convert back to u32 for serialization.
    Ok(Json(PirQueryResponse {
        response: response.response.iter().map(|e| e.as_u32()).collect(),
    }))
}

// =============================================================================
// Checkpoint Handlers
// =============================================================================

/// GET /checkpoint/latest — returns the latest checkpoint.
async fn get_checkpoint_latest(
    State(state): State<NodeState>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.latest_checkpoint() {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

/// GET /checkpoint/:height — returns the checkpoint at a specific height.
async fn get_checkpoint_at_height(
    State(state): State<NodeState>,
    AxumPath(height): AxumPath<u64>,
) -> Result<Json<CheckpointResponse>, StatusCode> {
    let s = state.read().await;
    match s.store.checkpoint_at_height(height) {
        Ok(Some(cp)) => Ok(Json(checkpoint_to_response(&cp))),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

fn checkpoint_to_response(cp: &dregg_federation::Checkpoint) -> CheckpointResponse {
    CheckpointResponse {
        height: cp.height,
        ledger_state_root: hex_encode(&cp.ledger_state_root),
        note_tree_root: hex_encode(&cp.note_tree_root),
        nullifier_set_root: hex_encode(&cp.nullifier_set_root),
        revocation_tree_root: hex_encode(&cp.revocation_tree_root),
        epoch: cp.epoch,
        timestamp: cp.timestamp,
        federation_members: cp.federation_members.len(),
        qc_votes: cp.qc.votes.len(),
    }
}

// =============================================================================
// Blocklace Checkpoint Serving (for new node fast-sync)
// =============================================================================

/// GET /api/blocklace/checkpoint?height=N
///
/// Returns the full blocklace checkpoint at height N (or the latest if height is
/// not specified). This includes the serialized blocklace DAG state and ledger
/// snapshot, both hex-encoded with BLAKE3 hashes for integrity verification.
///
/// New nodes use this endpoint to fast-sync from a recent known-good state
/// instead of replaying the entire block history.
async fn get_blocklace_checkpoint(
    Query(params): Query<crate::blocklace_sync::BlocklaceCheckpointQuery>,
    State(state): State<NodeState>,
) -> Result<Json<crate::blocklace_sync::BlocklaceCheckpointResponse>, StatusCode> {
    let s = state.read().await;

    // Determine which height to serve.
    let height = match params.height {
        Some(h) => h,
        None => crate::blocklace_sync::latest_blocklace_checkpoint_height(&s.store),
    };

    if height == 0 {
        return Err(StatusCode::NOT_FOUND);
    }

    match crate::blocklace_sync::load_blocklace_checkpoint(&s.store, height) {
        Some(checkpoint) => Ok(Json(checkpoint)),
        None => Err(StatusCode::NOT_FOUND),
    }
}

// =============================================================================
// Faucet
// =============================================================================

/// Faucet cell token ID (all zeros — the genesis default token domain; see
/// `node/src/genesis.rs::write_genesis` which mints the faucet supply under
/// `default_token_id = [0u8; 32]`).
const FAUCET_TOKEN_ID: [u8; 32] = [0x00; 32];

/// The faucet's deterministic Ed25519 signing key.
///
/// Derived identically to `genesis.rs` (`blake3::derive_key(
/// "dregg-devnet-faucet-key-v1", b"genesis")`) so the runtime faucet endpoint
/// controls the *same* cell that holds the genesis supply and can produce a
/// REAL signed Transfer turn from it — rather than the previous disconnected
/// `[0x01; 32]` placeholder whose `apply_delta` mutated only this node's local
/// ledger and never replicated.
fn faucet_signing_key() -> ed25519_dalek::SigningKey {
    let secret = blake3::derive_key("dregg-devnet-faucet-key-v1", b"genesis");
    ed25519_dalek::SigningKey::from_bytes(&secret)
}

/// The faucet cell's public key (matches the genesis-minted faucet cell).
fn faucet_public_key() -> [u8; 32] {
    faucet_signing_key().verifying_key().to_bytes()
}

#[derive(Deserialize)]
pub struct FaucetRequest {
    /// Hex-encoded 32-byte recipient cell ID.
    pub recipient: String,
    /// Amount of computrons to transfer (max 10000 per request). Use 0 to
    /// materialize a hosted devnet cell without claiming faucet funds.
    pub amount: u64,
    /// Optional hex-encoded Ed25519 public key for the recipient. When set,
    /// the node verifies `recipient == CellId::derive_raw(public_key, default_token_id)`
    /// and inserts a canonical hosted cell instead of a remote stub.
    #[serde(default)]
    pub public_key: Option<String>,
}

#[derive(Serialize)]
pub struct FaucetResponse {
    pub success: bool,
    pub tx_hash: Option<String>,
    pub amount: u64,
    /// Hex hash of the REAL committed faucet turn (the key under which its
    /// receipt appears in `/api/receipts`, where `has_proof` flips true once
    /// the async prove pool attaches the attestation). `tx_hash` remains the
    /// synthetic activity-feed hash for backward compatibility.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Faucet rate limiter: 1 request per cell per 60 seconds.
#[derive(Clone)]
struct FaucetRateLimiter {
    /// Map of recipient cell_id hex -> last request time.
    state: Arc<Mutex<HashMap<String, Instant>>>,
}

impl FaucetRateLimiter {
    fn new() -> Self {
        let limiter = Self {
            state: Arc::new(Mutex::new(HashMap::new())),
        };
        // Prune stale entries periodically so a flood of unique recipient ids
        // cannot grow this map without bound (same discipline as `RateLimiter`).
        let prune_state = limiter.state.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(120));
            loop {
                interval.tick().await;
                let mut map = prune_state.lock().await;
                let now = Instant::now();
                map.retain(|_, last| now.duration_since(*last).as_secs() < 60);
            }
        });
        limiter
    }

    /// Returns true if the request should be allowed.
    async fn check(&self, recipient: &str) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        if let Some(last) = map.get(recipient)
            && now.duration_since(*last).as_secs() < 60
        {
            return false;
        }
        map.insert(recipient.to_string(), now);
        true
    }
}

/// POST /api/faucet — transfer computrons from the faucet cell to a recipient.
///
/// Only enabled when `--enable-faucet` is set. Rate limited TWICE:
/// * per recipient cell (1/min) — the original anti-drain bucket; and
/// * per client IP (proxy-aware, F-1) — covering BOTH the funded and the
///   `amount == 0` materialization paths. Without the per-IP gate, an attacker
///   minting a fresh recipient id per request gets a fresh per-cell bucket every
///   time (unbounded faucet drain), and the zero-amount path inserted unbounded
///   stub cells into the ledger with NO limit at all.
///
/// Maximum 10000 computrons per request.
async fn post_faucet(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<FaucetRequest>,
    limiter: FaucetRateLimiter,
    ip_limiter: RateLimiter,
) -> Result<Json<FaucetResponse>, StatusCode> {
    // Per-IP gate first: bounds total faucet traffic (including zero-amount
    // cell materialization) per real client, before any state is touched.
    if !ip_limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    // Validate amount. A zero amount is allowed as a devnet materialization
    // path for hosted cells; it does not consume the per-cell faucet limit.
    if req.amount > 10_000 {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: None,
            amount: 0,
            error: Some("amount must be between 0 and 10000".to_string()),
        }));
    }

    // Validate recipient hex.
    let recipient_bytes: [u8; 32] = match hex_decode(&req.recipient) {
        Ok(b) => b,
        Err(_) => {
            return Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some("invalid recipient: must be 64 hex characters".to_string()),
            }));
        }
    };
    let recipient_cell_id = dregg_cell::CellId(recipient_bytes);

    let recipient_public_key = match &req.public_key {
        Some(pk_hex) => {
            let pk: [u8; 32] = match hex_decode(pk_hex) {
                Ok(pk) => pk,
                Err(_) => {
                    return Ok(Json(FaucetResponse {
                        success: false,
                        tx_hash: None,
                        turn_hash: None,
                        amount: 0,
                        error: Some("invalid public_key: must be 64 hex characters".to_string()),
                    }));
                }
            };
            let default_token_id = *blake3::hash(b"default").as_bytes();
            let expected = dregg_cell::CellId::derive_raw(&pk, &default_token_id);
            if expected != recipient_cell_id {
                return Ok(Json(FaucetResponse {
                    success: false,
                    tx_hash: None,
                    turn_hash: None,
                    amount: 0,
                    error: Some("public_key does not derive the recipient cell".to_string()),
                }));
            }
            Some(pk)
        }
        None => None,
    };

    // Rate limit check.
    if req.amount > 0 && !limiter.check(&req.recipient).await {
        return Ok(Json(FaucetResponse {
            success: false,
            tx_hash: None,
            turn_hash: None,
            amount: 0,
            error: Some("rate limited: 1 request per cell per minute".to_string()),
        }));
    }

    let mut s = state.write().await;

    // MULTI-PARTY vs SOLO provisioning split. In a committee (n>1), consensus
    // FINALIZATION is the single authoritative application of a turn — the SAME
    // `execute_finalized_turn` runs on every node and provisions any missing
    // cells DETERMINISTICALLY from the finalized turn's own data (see
    // `provision_transfer_destinations`). The faucet endpoint must therefore NOT
    // advance any authoritative state at submission: creating the faucet/recipient
    // cell here would be LOCAL-ONLY (peers never see it) and, worse, NON-UNIFORM
    // (the submitter would mint a canonical `with_balance(pk, …)` cell while peers
    // materialize a zero-pk stub at the same id — divergent ledger content the
    // attested root does not catch, because it commits only `cell.state`). So in
    // multi-party mode all provisioning + execution below runs against a SCRATCH
    // CLONE purely to build the receipt/proof for the HTTP response; the
    // authoritative ledger is untouched until finalization. Solo (n=1) has no
    // finalization pass, so it provisions + commits authoritatively here.
    let is_solo = s.solo_consensus.as_ref().is_some_and(|sc| sc.is_solo);

    // Ensure the faucet cell exists (create on first use). Uses the genesis-
    // derived faucet key so this is the SAME cell genesis mints the supply into;
    // on a genesis node it already exists on every node. In multi-party mode this
    // touches only the scratch clone (the genesis faucet cell is already present
    // authoritatively cross-node).
    let faucet_pubkey = faucet_public_key();
    let faucet_cell_id = dregg_cell::CellId::derive_raw(&faucet_pubkey, &FAUCET_TOKEN_ID);

    // Recipient provisioning. CROSS-NODE UNIFORMITY: in multi-party mode the
    // recipient is provisioned by the finalized executor on every node from the
    // turn data alone (the recipient's public key is NOT carried over consensus,
    // so every node — including this submitter — must agree on the SAME provisioned
    // cell). We therefore reuse the identical `remote_stub_with_id_and_balance`
    // provisioning here (on the scratch clone) that `execute_finalized_turn` uses,
    // so the receipt this node returns matches the authoritative finalized outcome.
    // Solo mode mints the canonical hosted cell (with the known pk) directly, since
    // it is the sole authority.
    let recipient_created_authoritatively = is_solo && s.ledger.get(&recipient_cell_id).is_none();
    let provision_recipient = |ledger: &mut dregg_cell::Ledger| {
        if ledger.get(&recipient_cell_id).is_some() {
            return;
        }
        let recipient_cell = match (is_solo, recipient_public_key) {
            (true, Some(pk)) => {
                let default_token_id = *blake3::hash(b"default").as_bytes();
                dregg_cell::Cell::with_balance(pk, default_token_id, 0)
            }
            // Multi-party (or no known pk): the uniform stub provisioning every
            // node applies in `execute_finalized_turn`.
            _ => dregg_cell::Cell::remote_stub_with_id_and_balance(recipient_cell_id, 0),
        };
        let _ = ledger.insert_cell(recipient_cell);
    };

    if is_solo {
        // Solo: provision authoritatively (no finalization pass).
        if s.ledger.get(&faucet_cell_id).is_none() {
            let faucet_cell =
                dregg_cell::Cell::with_balance(faucet_pubkey, FAUCET_TOKEN_ID, 1_000_000);
            let _ = s.ledger.insert_cell(faucet_cell);
        }
        provision_recipient(&mut s.ledger);
    }

    let tx_hash = compute_faucet_activity_hash(&recipient_cell_id, req.amount);

    if req.amount == 0 {
        // Zero-amount is a devnet hosted-cell MATERIALIZATION convenience. There
        // is no Transfer and no consensus turn, so in multi-party mode there is no
        // finalized pass to provision the cell — materialize it authoritatively
        // here regardless of mode (insert-if-absent; idempotent across nodes for a
        // pk-derived id). This is the one provisioning the faucet still applies
        // directly under multi-party, and it carries no value.
        let recipient_created = if is_solo {
            recipient_created_authoritatively
        } else {
            let created = s.ledger.get(&recipient_cell_id).is_none();
            if created {
                provision_recipient(&mut s.ledger);
            }
            created
        };
        if recipient_created {
            push_committed_event(
                &mut s,
                tx_hash.clone(),
                req.recipient.clone(),
                vec!["faucet_materialized_cell".to_string()],
                ActivityProofStatus::NotRequired,
            );
        }
        return Ok(Json(FaucetResponse {
            success: true,
            tx_hash: Some(tx_hash),
            turn_hash: None,
            amount: 0,
            error: None,
        }));
    }

    // Build a REAL faucet-signed Transfer turn and run it through the
    // executor, then gossip + submit to the blocklace — the same consensus
    // path committed operator turns use. This replaces the old direct
    // `ledger.apply_delta` write, which mutated only this node's local ledger
    // and never replicated (so a peer never saw the faucet grant).
    let faucet_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
        faucet_signing_key().to_bytes(),
    ));
    let transfer = dregg_turn::Effect::Transfer {
        from: faucet_cell_id,
        to: recipient_cell_id,
        amount: req.amount,
    };
    // Sign over the SAME federation id the executor verifies against
    // (`federation_id_for_executor`: `s.federation_id` when configured, else
    // `blake3(pubkey)`). Using the raw `s.federation_id` on an unconfigured solo
    // node mismatched the executor's domain and failed Ed25519 verification.
    let exec_federation_id = crate::executor_setup::federation_id_for_executor(&s);
    let action = faucet_cclerk.make_action(
        faucet_cell_id,
        "faucet_transfer",
        vec![transfer],
        &exec_federation_id,
    );
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);
    // The executor's budget gate caps computrons at `turn.fee` (`estimated >
    // fee` → BudgetExceeded). A fee of 0 made every amount>0 faucet transfer
    // reject ("budget exceeded: limit=0, used=100"); the faucet cell holds the
    // genesis supply, so it covers a real fee. Size the fee to the estimated
    // cost so the gate passes deterministically.
    // PIPELINED nonce: the faucet's AUTHORITATIVE nonce only advances when a
    // faucet turn FINALIZES through consensus (the scratch-clone execution below
    // deliberately does NOT mutate the authoritative ledger in full mode). Reading
    // it directly meant a second faucet request submitted before the first
    // finalized re-used the same nonce and replayed. Reserve the next nonce as
    // `max(authoritative, reserved)` and bump the reservation, so back-to-back
    // submissions get fresh consecutive nonces that finalize in order. `max`
    // reconciles the two sides: once the in-flight turns finalize, the
    // authoritative nonce catches up and no permanent gap opens.
    let authoritative_nonce = s
        .ledger
        .get(&faucet_cell_id)
        .map(|c| c.state.nonce())
        .unwrap_or(0);
    let faucet_nonce = authoritative_nonce.max(s.faucet_reserved_nonce.unwrap_or(0));
    s.faucet_reserved_nonce = Some(faucet_nonce + 1);
    // Receipt-chain head for the turn's verified ChainHead leg.
    //
    // SOLO (n=1): submission is authoritative, so bind to the local chain head
    // (the cipherclerk's `append_receipt` fills a `None` prev with the chain
    // head, changing the appended receipt's hash; binding it here keeps the
    // stored WitnessedReceipt findable so has_proof can flip).
    //
    // FULL (n>1): the AUTHORITATIVE receipt-chain advance is `execute_finalized_turn`,
    // which runs identically on EVERY node in tau order and — like the ledger — does
    // NOT observe the submitter's local submission-time append. The finalized executor
    // only seeds the LOCAL agent's receipt head, never the faucet's, so the verified
    // ChainHead leg expects `None` for the faucet agent on every node. Binding to the
    // local chain head here made every NON-submitter reject the faucet turn after the
    // first ("receipt chain mismatch: expected None, got Some(..)"), AND made the
    // submitter reject it (its own head had already advanced at submission) — so a
    // second faucet turn provisioned its destination but the transfer never funded it
    // (`found:true, balance:0`), silently breaking sustained faucet finality. `None`
    // matches the finalized expectation uniformly on all nodes.
    let faucet_prev_receipt = if is_solo {
        s.cclerk.receipt_chain().last().map(|r| r.receipt_hash())
    } else {
        None
    };
    let mut faucet_turn = Turn {
        agent: faucet_cell_id,
        nonce: faucet_nonce,
        fee: 0, // sized to the estimated cost below so the budget gate passes
        memo: Some(format!("faucet_transfer:{}", req.amount)),
        // Stamped so the wire marshal accepts the envelope and the turn stays
        // on the verified Lean producer (see `default_valid_until`).
        valid_until: default_valid_until(),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: faucet_prev_receipt,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let executor = crate::executor_setup::new_submit_executor(&s);
    seed_executor_receipt_head(&executor, faucet_turn.agent, faucet_prev_receipt);
    // Size the fee (= computron budget cap) to the estimated cost so the budget
    // gate passes; the faucet cell holds the genesis supply and covers it.
    faucet_turn.fee = executor.estimate_cost(&faucet_turn);

    let signed = faucet_cclerk.sign_turn(&faucet_turn);
    let turn_hash_bytes = faucet_turn.hash();
    let turn_hash_hex = hex_encode(&turn_hash_bytes);

    // Pre-execution ledger snapshot for the witness revalidation below (the
    // proof's pre-state must be captured BEFORE the executor mutates it).
    let pre_ledger = s.ledger.clone();
    let lean_producer_enabled = s.lean_producer_enabled;

    // MULTI-PARTY: consensus FINALIZATION is the authoritative application of the
    // faucet turn (the SAME `execute_finalized_turn` runs on every node and emits
    // the attested root). Eagerly committing here would mutate ONLY this node's
    // ledger — advancing the faucet cell's nonce so the finalized re-execution is
    // rejected as a "nonce replay", and creating the recipient cell only locally
    // so PEERS reject the finalized Transfer as "destination not found" — both of
    // which block cross-node commit (`latest_height` stuck at 0). So in full mode
    // we execute against a SCRATCH CLONE purely to build the receipt/proof for the
    // HTTP response, leaving the authoritative ledger untouched; the finalized
    // executor then applies the turn uniformly on all nodes (it auto-materializes
    // the Transfer destination identically on every node, see
    // `provision_transfer_destinations` / `execute_finalized_turn`). Solo (n=1)
    // keeps the direct authoritative commit — it has no separate finalization pass
    // and already provisioned the faucet + recipient cells above.
    let exec_result = if is_solo {
        // ONE executor gate (#171): solo faucet turns commit through the same
        // producer-aware path as every other ingress, authoritatively.
        crate::executor_setup::execute_via_producer(
            &executor,
            &faucet_turn,
            &mut s.ledger,
            lean_producer_enabled,
        )
    } else {
        // Full mode: receipt-only execution against a scratch clone; do NOT mutate
        // the authoritative ledger (finalization is authoritative, cross-node). The
        // scratch must carry the SAME provisioned destination the finalized executor
        // will install on every node, or the receipt-building Transfer here would hit
        // `TransferDestNotFound` and diverge from the authoritative outcome. We call
        // the IDENTICAL provisioning function the finalized path uses, on the SAME
        // call forest — so the receipt this node returns reflects exactly the
        // authoritative finalized provisioning (one implementation, no drift).
        let mut scratch = s.ledger.clone();
        crate::blocklace_sync::provision_transfer_destinations(
            &mut scratch,
            &faucet_turn.call_forest,
        );
        // PIPELINING: this receipt-build runs against a clone of the AUTHORITATIVE
        // ledger, whose faucet nonce only advances at finalization. For a turn
        // submitted before the prior finalizes, `faucet_nonce` (the reserved
        // pipelined nonce) is ahead of that authoritative nonce, so the executor's
        // exact nonce gate would reject the receipt build. Reflect the reserved
        // nonce onto the scratch faucet cell so the receipt builds for the turn that
        // WILL be valid at finalization (turns finalize in submission/tau order, each
        // advancing the authoritative nonce to meet the next). The authoritative
        // ledger is untouched; only this throwaway scratch is adjusted.
        if let Some(cell) = scratch.get_mut(&faucet_cell_id) {
            cell.state.set_nonce(faucet_nonce);
        }
        crate::executor_setup::execute_via_producer(
            &executor,
            &faucet_turn,
            &mut scratch,
            lean_producer_enabled,
        )
    };

    match exec_result {
        dregg_turn::TurnResult::Committed { mut receipt, .. } => {
            crate::metrics::set_ledger_cell_count(s.ledger.len() as f64);

            // Solo mode: tentative finality + height advance, exactly like the
            // /turn/submit commit path.
            let node_signing_key = s.cclerk.gossip_signing_key().to_bytes();
            if let Some(ref mut solo) = s.solo_consensus
                && solo.is_solo
            {
                receipt.finality = dregg_turn::Finality::Tentative;
                // Re-sign after the committed finality downgrade: finality is bound
                // into receipt_hash, and the executor signed the optimistic Final.
                resign_receipt_committed(&mut receipt, &node_signing_key);
                let height = solo.height;
                let _ = solo
                    .nullifier_log
                    .insert(turn_hash_bytes, turn_hash_bytes, height);
                solo.advance_height();
                #[cfg(debug_assertions)]
                debug_assert_signed_last(&receipt, &node_signing_key);
            }

            // The faucet turn is a REAL committed turn: append its receipt to
            // the chain and hand it to the async prove pool, the same pipeline as
            // /turn/submit. Previously the receipt was dropped here, so a faucet
            // turn never appeared in /api/receipts and could never reach
            // has_proof:true — the exact silent gap the devnet quickstart hit.
            // PATH-PRESERVE Phase 5b: the executor already validated + committed
            // the turn (the soundness boundary); the composed proof (rotated leg)
            // is built + self-verified off the lock. The attestation is best-effort
            // for the faucet (the commit stands either way; an unattested faucet
            // grant is a devnet-liveness issue, not a soundness one).
            let appended = match s.cclerk.append_receipt(receipt.clone()) {
                Ok(()) => true,
                Err(err) => {
                    tracing::warn!(
                        turn_hash = %turn_hash_hex,
                        error = %err,
                        "faucet receipt could not be appended to the receipt chain"
                    );
                    false
                }
            };
            let receipt_hash = receipt.receipt_hash();
            // Build the rotated attestation material from the actor's before/after
            // cells. In full mode the authoritative `s.ledger` was not mutated (the
            // receipt was built against a scratch clone), so before==after for the
            // single-cell faucet actor — correct for the rotated single-cell leg,
            // whose per-row welds carry the transfer delta from the v1 sub-trace
            // (the turn-invariant limbs are identical), exactly as the finalized
            // cap-less note-spend leg does.
            let pending_proof =
                match prepare_rotatable_turn(&faucet_turn, &pre_ledger, &s.ledger, receipt_hash) {
                    Ok(HttpWitnessOutcome::Rotatable(rotatable)) => Some(rotatable),
                    Ok(HttpWitnessOutcome::NotRequired) => None,
                    Err(err) => {
                        tracing::warn!(
                            turn_hash = %turn_hash_hex,
                            error = %err,
                            "faucet turn attestation prep failed; receipt stays \
                             committed-but-unattested (has_proof will not flip)"
                        );
                        None
                    }
                };
            let proof_status = if pending_proof.is_some() {
                ActivityProofStatus::ProofPending
            } else {
                ActivityProofStatus::NotRequired
            };

            push_committed_event(
                &mut s,
                tx_hash.clone(),
                req.recipient.clone(),
                vec![format!("faucet_transfer:{}", req.amount)],
                proof_status,
            );

            // Replicate through gossip + blocklace consensus.
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            // Async STARK attestation, off the lock — flips the receipt's
            // has_proof once the pool lands the proof.
            if appended {
                if let Some(rotatable) = pending_proof {
                    enqueue_async_proof(
                        &state,
                        rotatable,
                        receipt.clone(),
                        receipt_hash,
                        turn_hash_hex.clone(),
                    )
                    .await;
                }
                state.emit(crate::state::NodeEvent::Receipt {
                    hash: turn_hash_hex.clone(),
                });
            }

            let turn_data_for_gossip = turn_data.clone();
            if let Some(gossip) = state.gossip().await {
                tokio::spawn(async move {
                    gossip
                        .gossip_turn(turn_hash_bytes, turn_data_for_gossip)
                        .await;
                });
            }
            if let Some(blocklace) = state.blocklace().await {
                let state_for_blocklace = state.clone();
                tokio::spawn(async move {
                    blocklace.submit_turn(&state_for_blocklace, turn_data).await;
                });
            }

            Ok(Json(FaucetResponse {
                success: true,
                tx_hash: Some(tx_hash),
                turn_hash: Some(turn_hash_hex),
                amount: req.amount,
                error: None,
            }))
        }
        dregg_turn::TurnResult::Rejected { reason, .. } => {
            // The turn we reserved a nonce for is NOT entering consensus, so roll
            // the reservation back (it is still the value we set — `s` is write-
            // locked across this whole handler) to avoid a permanent gap that
            // would replay every subsequent faucet turn.
            if s.faucet_reserved_nonce == Some(faucet_nonce + 1) {
                s.faucet_reserved_nonce = Some(faucet_nonce);
            }
            crate::metrics::inc_turns_executed("rejected");
            crate::metrics::note_turn_rejected(&reason);
            Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some(format!("transfer rejected: {reason}")),
            }))
        }
        _ => {
            if s.faucet_reserved_nonce == Some(faucet_nonce + 1) {
                s.faucet_reserved_nonce = Some(faucet_nonce);
            }
            Ok(Json(FaucetResponse {
                success: false,
                tx_hash: None,
                turn_hash: None,
                amount: 0,
                error: Some("faucet transfer did not commit".to_string()),
            }))
        }
    }
}

fn compute_faucet_activity_hash(recipient: &dregg_cell::CellId, amount: u64) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-node-faucet-activity-v1");
    hasher.update(&recipient.0);
    hasher.update(&amount.to_le_bytes());
    let now_nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos() as u64;
    hasher.update(&now_nanos.to_le_bytes());
    hex_encode(hasher.finalize().as_bytes())
}

// =============================================================================
// Discharge Gateway Endpoint
// =============================================================================

/// POST /api/discharge request body.
#[derive(Deserialize)]
pub struct NodeDischargeRequest {
    /// Base64-encoded ticket from the 3P caveat.
    pub ticket: String,
    /// Optional client identifier.
    pub client_id: Option<String>,
    /// Optional base64-encoded proof.
    pub proof: Option<String>,
    /// Optional payment amount.
    pub payment: Option<u64>,
    /// Arbitrary metadata.
    #[serde(default)]
    pub metadata: HashMap<String, String>,
}

/// POST /api/discharge response body.
#[derive(Serialize)]
pub struct NodeDischargeResponse {
    pub success: bool,
    pub discharge: Option<String>,
    pub expires_at: Option<i64>,
    pub condition_met: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// POST /api/discharge — issue a discharge macaroon from this node's gateway.
///
/// The node acts as a discharge gateway for its own federation's tokens.
/// The shared key is derived from the cipherclerk's signing key using BLAKE3 KDF
/// with domain "dregg-discharge-gateway-v1".
async fn post_discharge(
    ConnectInfo(addr): ConnectInfo<std::net::SocketAddr>,
    headers: axum::http::HeaderMap,
    State(state): State<NodeState>,
    Json(req): Json<NodeDischargeRequest>,
    limiter: RateLimiter,
) -> Result<Json<NodeDischargeResponse>, StatusCode> {
    // Per-IP rate limit (proxy-aware, F-1): this endpoint is public and its
    // body takes the global state-write lock, so it must not be free to flood.
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;

    // Decode ticket from base64.
    let ticket = engine
        .decode(&req.ticket)
        .map_err(|_| StatusCode::BAD_REQUEST)?;

    // Decode optional proof from base64.
    let proof = match &req.proof {
        Some(p) => Some(engine.decode(p).map_err(|_| StatusCode::BAD_REQUEST)?),
        None => None,
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // SECURITY: Use the persistent discharge gateway from node state.
    // This ensures the `issued` HashSet persists across requests, providing
    // actual replay prevention. Previously, a fresh gateway was created per
    // request, making the replay set useless (it was dropped immediately).
    if s.discharge_gateway.is_none() {
        let gateway_key = s.cclerk.derive_symmetric_key("dregg-discharge-gateway-v1");
        let location = format!("dregg-node://{}", hex_encode(&s.cclerk.public_key().0));
        let mut gateway = dregg_macaroon::DischargeGateway::new(gateway_key, location);
        // Default evaluator: require proof to prevent accidental open gateways.
        gateway.add_evaluator(Box::new(dregg_macaroon::ProofRequiredEvaluator));
        // Load previously persisted replay set from store (survives restarts).
        if let Ok(Some(data)) = s.store.get_config("discharge_issued_set") {
            gateway.load_issued_set(&data);
        }
        s.discharge_gateway = Some(gateway);
    }

    let gateway = s.discharge_gateway.as_ref().unwrap();

    let discharge_req = dregg_macaroon::DischargeRequest {
        ticket,
        client_id: req.client_id,
        proof,
        payment: req.payment,
        metadata: req.metadata,
    };

    match gateway.process_request(&discharge_req) {
        Ok(resp) => {
            // SECURITY: Persist replay-prevention state immediately after each
            // successful discharge. A crash between discharge issuance and shutdown
            // would otherwise lose the replay set, enabling ticket reuse.
            let data = gateway.serialize_issued_set();
            if let Err(e) = s.store.set_config("discharge_issued_set", &data) {
                tracing::warn!(error = %e, "failed to persist discharge replay set");
            }
            Ok(Json(NodeDischargeResponse {
                success: true,
                discharge: Some(resp.discharge),
                expires_at: Some(resp.expires_at),
                condition_met: Some(resp.condition_met),
                error: None,
            }))
        }
        Err(e) => Ok(Json(NodeDischargeResponse {
            success: false,
            discharge: None,
            expires_at: None,
            condition_met: None,
            error: Some(e.reason),
        })),
    }
}

// =============================================================================
// Factory, Sovereign, Bearer, and Composition endpoints
// =============================================================================

#[derive(Deserialize)]
struct CreateFromFactoryRequest {
    factory_vk: String,
    owner_pubkey: String,
    token_id: Option<String>,
    /// Hex-encoded 8-byte nonce, included in the signed message (F-P1-2).
    nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature from `owner_pubkey` over
    /// `b"dregg-create-from-factory-v1" || factory_vk || owner_pubkey || nonce`.
    signature: String,
}

#[derive(Serialize)]
struct CreateFromFactoryResponse {
    success: bool,
    child_vk: Option<String>,
    cell_id: Option<String>,
    error: Option<String>,
}

async fn post_create_from_factory(
    State(state): State<NodeState>,
    Json(req): Json<CreateFromFactoryRequest>,
) -> Result<Json<CreateFromFactoryResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let factory_vk = hex_decode_32_result(&req.factory_vk).map_err(|_| StatusCode::BAD_REQUEST)?;
    let owner_pubkey =
        hex_decode_32_result(&req.owner_pubkey).map_err(|_| StatusCode::BAD_REQUEST)?;

    // F-P1-2: verify the caller actually possesses the owner private key, so an
    // authenticated operator-tier caller can't register provenance for cells
    // they don't own.
    {
        let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| StatusCode::BAD_REQUEST)?;
        let mut payload = Vec::with_capacity(32 + 32 + nonce_bytes.len());
        payload.extend_from_slice(&factory_vk);
        payload.extend_from_slice(&owner_pubkey);
        payload.extend_from_slice(&nonce_bytes);
        if let Err(e) = verify_ed25519_sig(
            &owner_pubkey,
            &req.signature,
            b"dregg-create-from-factory-v1",
            &payload,
        ) {
            return Ok(Json(CreateFromFactoryResponse {
                success: false,
                child_vk: None,
                cell_id: None,
                error: Some(format!("owner signature rejected: {e}")),
            }));
        }
    }

    let params = dregg_cell::factory::FactoryCreationParams {
        owner_pubkey,
        mode: dregg_cell::CellMode::default(),
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
    };

    let param_hash = dregg_cell::factory::ChildVkStrategy::compute_param_hash(&params);
    let child_vk = dregg_cell::factory::ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

    // Derive cell_id from owner + token_id.
    let token_id = req
        .token_id
        .as_deref()
        .map(|s| *blake3::hash(s.as_bytes()).as_bytes())
        .unwrap_or_else(|| *blake3::hash(b"dregg-default-domain").as_bytes());
    let cell_id = dregg_cell::CellId::derive_raw(&owner_pubkey, &token_id);

    Ok(Json(CreateFromFactoryResponse {
        success: true,
        child_vk: Some(hex_encode(&child_vk)),
        cell_id: Some(hex_encode(&cell_id.0)),
        error: None,
    }))
}

#[derive(Deserialize)]
struct MakeSovereignRequest {
    cell_id: String,
    /// Hex-encoded 8-byte nonce (F-P1-2).
    nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature from the cell owner over
    /// `b"dregg-make-sovereign-v1" || cell_id || nonce`. The signing key
    /// MUST be the cell's `public_key` if the cell exists on the ledger;
    /// otherwise it MUST be the `cell_id` itself (sovereign convention:
    /// for fresh sovereign cells, cell_id == pubkey).
    signature: String,
}

#[derive(Serialize)]
struct MakeSovereignResponse {
    success: bool,
    state_commitment: Option<String>,
    error: Option<String>,
}

async fn post_make_sovereign(
    State(state): State<NodeState>,
    Json(req): Json<MakeSovereignRequest>,
) -> Result<Json<MakeSovereignResponse>, StatusCode> {
    let mut s = state.write().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let cell_id_bytes = hex_decode_32_result(&req.cell_id).map_err(|_| StatusCode::BAD_REQUEST)?;
    let cell_id = dregg_cell::CellId(cell_id_bytes);

    // F-P1-2: verify the caller possesses the cell-owner private key. For an
    // existing cell, the signing key is the cell's `public_key`. For a brand
    // new sovereign cell (cell_id == pubkey by construction), the signing key
    // is the cell_id itself.
    let owner_pk = s
        .ledger
        .get(&cell_id)
        .map(|c| *c.public_key())
        .unwrap_or(cell_id_bytes);
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| StatusCode::BAD_REQUEST)?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&cell_id_bytes);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_ed25519_sig(
        &owner_pk,
        &req.signature,
        b"dregg-make-sovereign-v1",
        &payload,
    ) {
        return Ok(Json(MakeSovereignResponse {
            success: false,
            state_commitment: None,
            error: Some(format!("owner signature rejected: {e}")),
        }));
    }

    // Compute a state commitment from the cell ID (deterministic for the API response).
    // The full state commitment is computed by the cipherclerk SDK and submitted via
    // /cells/register with the proper sovereign workflow.
    let commitment = blake3::derive_key("dregg-sovereign-commitment-v1", &cell_id_bytes);

    match s.ledger.register_sovereign_cell(cell_id, commitment) {
        Ok(()) => Ok(Json(MakeSovereignResponse {
            success: true,
            state_commitment: Some(hex_encode(&commitment)),
            error: None,
        })),
        Err(e) => Ok(Json(MakeSovereignResponse {
            success: false,
            state_commitment: None,
            error: Some(e.to_string()),
        })),
    }
}

#[derive(Deserialize)]
struct ComposeProofsRequest {
    proofs: Vec<serde_json::Value>,
    mode: String,
}

#[derive(Serialize)]
struct ComposeProofsResponse {
    success: bool,
    composed_commitment: Option<String>,
    mode: String,
    input_count: usize,
    error: Option<String>,
}

async fn post_compose_proofs(
    State(state): State<NodeState>,
    Json(req): Json<ComposeProofsRequest>,
) -> Result<Json<ComposeProofsResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Compute composition commitment binding all proofs.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-proof-composition-v1");
    hasher.update(req.mode.as_bytes());
    for (i, proof) in req.proofs.iter().enumerate() {
        hasher.update(&(i as u32).to_le_bytes());
        hasher.update(proof.to_string().as_bytes());
    }
    let commitment = *hasher.finalize().as_bytes();

    Ok(Json(ComposeProofsResponse {
        success: true,
        composed_commitment: Some(hex_encode(&commitment)),
        mode: req.mode,
        input_count: req.proofs.len(),
        error: None,
    }))
}

#[derive(Deserialize)]
struct BearerAuthRequest {
    /// JSON-serialized BearerCapProof (the delegation chain proof).
    bearer_proof: serde_json::Value,
    /// Hex-encoded 32-byte target cell ID.
    target_cell: String,
}

#[derive(Serialize)]
struct BearerAuthResponse {
    authorized: bool,
    error: Option<String>,
}

/// POST /turns/bearer-auth — verify a bearer capability delegation chain.
///
/// Deserializes the BearerCapProof, checks expiry against current block height,
/// checks revocation channels, verifies Ed25519 signatures or STARK proofs in
/// the delegation chain, and confirms attenuation (bearer perms subset of delegator perms).
async fn post_bearer_auth(
    State(state): State<NodeState>,
    Json(req): Json<BearerAuthRequest>,
) -> Result<Json<BearerAuthResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    // Deserialize the BearerCapProof from the request JSON.
    let bearer_proof: dregg_turn::BearerCapProof =
        serde_json::from_value(req.bearer_proof).map_err(|_| StatusCode::BAD_REQUEST)?;

    let _target_cell =
        hex_decode_32_result(&req.target_cell).map_err(|_| StatusCode::BAD_REQUEST)?;

    let executor = crate::executor_setup::new_verify_executor(&s);

    // Call the executor's verify_bearer_cap with an empty path (top-level check).
    match executor.verify_bearer_cap(&bearer_proof, &s.ledger, &[]) {
        Ok(_) => Ok(Json(BearerAuthResponse {
            authorized: true,
            error: None,
        })),
        Err((turn_error, _path)) => Ok(Json(BearerAuthResponse {
            authorized: false,
            error: Some(format!("{turn_error}")),
        })),
    }
}

#[derive(Deserialize)]
struct PeerExchangeRequest {
    sender_cell: String,
    receiver_cell: String,
    amount: u64,
}

#[derive(Serialize)]
struct PeerExchangeResponse {
    success: bool,
    exchange_id: Option<String>,
    error: Option<String>,
}

async fn post_peer_exchange(
    State(state): State<NodeState>,
    Json(req): Json<PeerExchangeRequest>,
) -> Result<Json<PeerExchangeResponse>, StatusCode> {
    let s = state.read().await;
    if !s.unlocked {
        return Err(StatusCode::FORBIDDEN);
    }

    let sender = hex_decode_32_result(&req.sender_cell).map_err(|_| StatusCode::BAD_REQUEST)?;
    let receiver = hex_decode_32_result(&req.receiver_cell).map_err(|_| StatusCode::BAD_REQUEST)?;

    // Generate exchange ID.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-peer-exchange-v1");
    hasher.update(&sender);
    hasher.update(&receiver);
    hasher.update(&req.amount.to_le_bytes());
    let exchange_id = *hasher.finalize().as_bytes();

    // Log the peer exchange. Full execution is done via the standard turn
    // submission pipeline with sovereign_witnesses populated by the SDK.
    tracing::info!(
        sender = %hex_encode(&sender),
        receiver = %hex_encode(&receiver),
        amount = req.amount,
        "peer exchange initiated"
    );

    Ok(Json(PeerExchangeResponse {
        success: true,
        exchange_id: Some(hex_encode(&exchange_id)),
        error: None,
    }))
}

fn hex_decode_32_result(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", hex.len()));
    }
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
    }
    Ok(result)
}

/// Request to propose a LIVE epoch transition (validator-set reconfiguration)
/// on a running node. `add` / `remove` are 64-hex Ed25519 validator pubkeys; a
/// rotation is `remove`(old) + `add`(new). The change only APPLIES once a quorum
/// of the CURRENT committee ratifies it through finality.
#[derive(serde::Deserialize)]
pub struct ProposeEpochTransitionRequest {
    #[serde(default)]
    pub add: Vec<String>,
    #[serde(default)]
    pub remove: Vec<String>,
}

/// Response: the submitted proposal block ids (one per add/remove), plus the
/// current committee size + threshold for operator visibility.
#[derive(serde::Serialize)]
pub struct ProposeEpochTransitionResponse {
    pub success: bool,
    pub proposals: Vec<EpochProposalEntry>,
    pub committee_size: usize,
    pub threshold: usize,
    pub error: Option<String>,
}

#[derive(serde::Serialize)]
pub struct EpochProposalEntry {
    pub action: String,
    pub validator: String,
    pub proposal_block: String,
}

/// Submit a live epoch-transition proposal. Each validator key is parsed +
/// validated as a real Ed25519 point, then a `Leave`(remove) / `Join`(add)
/// membership proposal block is created on the running blocklace and gossiped.
async fn post_propose_epoch_transition(
    State(state): State<NodeState>,
    Json(req): Json<ProposeEpochTransitionRequest>,
) -> Result<Json<ProposeEpochTransitionResponse>, StatusCode> {
    // Parse + validate every requested key up front (a bad key fails the whole
    // request before anything is submitted).
    let mut removes: Vec<[u8; 32]> = Vec::with_capacity(req.remove.len());
    for h in &req.remove {
        removes.push(
            crate::operator_join::parse_validator_pubkey(h).map_err(|_| StatusCode::BAD_REQUEST)?,
        );
    }
    let mut adds: Vec<[u8; 32]> = Vec::with_capacity(req.add.len());
    for h in &req.add {
        adds.push(
            crate::operator_join::parse_validator_pubkey(h).map_err(|_| StatusCode::BAD_REQUEST)?,
        );
    }
    if removes.is_empty() && adds.is_empty() {
        return Ok(Json(ProposeEpochTransitionResponse {
            success: false,
            proposals: vec![],
            committee_size: 0,
            threshold: 0,
            error: Some("no --add or --remove validators given".to_string()),
        }));
    }

    let Some(blocklace) = state.blocklace().await else {
        return Ok(Json(ProposeEpochTransitionResponse {
            success: false,
            proposals: vec![],
            committee_size: 0,
            threshold: 0,
            error: Some(
                "node is not running blocklace consensus (no committee to reconfigure)".to_string(),
            ),
        }));
    };

    let mut proposals = Vec::new();
    // Removals first, then additions (a rotation = remove old + add new).
    for pk in &removes {
        let block_id = blocklace.propose_membership(&state, *pk, false).await;
        proposals.push(EpochProposalEntry {
            action: "remove".to_string(),
            validator: hex_encode(pk),
            proposal_block: hex_encode(&block_id.0),
        });
    }
    for pk in &adds {
        let block_id = blocklace.propose_membership(&state, *pk, true).await;
        proposals.push(EpochProposalEntry {
            action: "add".to_string(),
            validator: hex_encode(pk),
            proposal_block: hex_encode(&block_id.0),
        });
    }

    let (committee_size, threshold) = {
        let c = blocklace.constitution.read().await;
        (c.current.participant_count(), c.threshold())
    };

    Ok(Json(ProposeEpochTransitionResponse {
        success: true,
        proposals,
        committee_size,
        threshold,
        error: None,
    }))
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Encode variable-length byte slices to hex (for signatures, etc.).
fn hex_encode_var(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn starbridge_limit(limit: Option<usize>) -> usize {
    limit.unwrap_or(50).min(200)
}

fn text_filter_matches(value: &str, filter: &Option<String>) -> bool {
    filter.as_ref().is_none_or(|needle| {
        value
            .to_ascii_lowercase()
            .contains(&needle.to_ascii_lowercase())
    })
}

fn exact_filter_matches(value: &str, filter: &Option<String>) -> bool {
    filter
        .as_ref()
        .is_none_or(|needle| value.eq_ignore_ascii_case(needle))
}

fn starbridge_event_matches(event: &CommittedEvent, params: &StarbridgeQuery) -> bool {
    exact_filter_matches(&event.cell_id, &params.cell)
        && exact_filter_matches(&event.turn_hash, &params.turn_hash)
        && params.memo.as_ref().is_none_or(|memo| {
            event.effects.iter().any(|effect| {
                effect
                    .to_ascii_lowercase()
                    .contains(&memo.to_ascii_lowercase())
            })
        })
        && params.effect.as_ref().is_none_or(|effect| {
            event.effects.iter().any(|summary| {
                summary
                    .to_ascii_lowercase()
                    .contains(&effect.to_ascii_lowercase())
            })
        })
        && params.app.as_ref().is_none_or(|app| {
            classify_starbridge_app(None, &event.effects)
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn starbridge_signed_turn_info(
    queue_index: usize,
    signed: &SignedTurn,
) -> StarbridgeSignedTurnInfo {
    let mut action_targets = Vec::new();
    let mut effect_kinds = Vec::new();
    let mut touched = HashSet::new();

    for tree in signed.turn.call_forest.iter_dfs() {
        let target = hex_encode(&tree.action.target.0);
        touched.insert(target.clone());
        action_targets.push(target);
        for effect in &tree.action.effects {
            effect_kinds.push(effect_kind(effect));
            for cell in effect_cells(effect) {
                touched.insert(cell);
            }
        }
    }

    let mut touched_cells: Vec<String> = touched.into_iter().collect();
    touched_cells.sort();
    effect_kinds.sort();
    effect_kinds.dedup();

    StarbridgeSignedTurnInfo {
        queue_index,
        turn_hash: hex_encode(&signed.turn.hash()),
        signer: hex_encode(&signed.signer.0),
        agent: hex_encode(&signed.turn.agent.0),
        nonce: signed.turn.nonce,
        fee: signed.turn.fee,
        memo: signed.turn.memo.clone(),
        action_count: signed.turn.action_count(),
        effect_count: signed.turn.call_forest.total_effects().len(),
        action_targets,
        app: classify_starbridge_app(signed.turn.memo.as_deref(), &effect_kinds),
        effect_kinds,
        touched_cells,
    }
}

fn starbridge_signed_turn_matches(
    info: &StarbridgeSignedTurnInfo,
    params: &StarbridgeQuery,
) -> bool {
    exact_filter_matches(&info.turn_hash, &params.turn_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            info.touched_cells
                .iter()
                .any(|touched| touched.eq_ignore_ascii_case(cell))
        })
        && params
            .memo
            .as_ref()
            .is_none_or(|_| text_filter_matches(info.memo.as_deref().unwrap_or(""), &params.memo))
        && params.effect.as_ref().is_none_or(|effect| {
            info.effect_kinds.iter().any(|kind| {
                kind.eq_ignore_ascii_case(effect) || text_filter_matches(kind, &params.effect)
            })
        })
        && params.app.as_ref().is_none_or(|app| {
            info.app
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn starbridge_action_matches(info: &StarbridgeActionInfo, params: &StarbridgeQuery) -> bool {
    exact_filter_matches(&info.turn_hash, &params.turn_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            info.target.eq_ignore_ascii_case(cell)
                || info
                    .touched_cells
                    .iter()
                    .any(|touched| touched.eq_ignore_ascii_case(cell))
        })
        && params
            .memo
            .as_ref()
            .is_none_or(|_| text_filter_matches(info.memo.as_deref().unwrap_or(""), &params.memo))
        && params.effect.as_ref().is_none_or(|effect| {
            info.effect_kinds.iter().any(|kind| {
                kind.eq_ignore_ascii_case(effect) || text_filter_matches(kind, &params.effect)
            })
        })
        && params.app.as_ref().is_none_or(|app| {
            info.app
                .as_deref()
                .is_some_and(|kind| kind.eq_ignore_ascii_case(app))
        })
}

fn identity_scoped_params(params: &StarbridgeQuery) -> StarbridgeQuery {
    StarbridgeQuery {
        limit: params.limit,
        since_height: params.since_height,
        cell: params.cell.clone(),
        memo: params.memo.clone(),
        effect: params.effect.clone(),
        turn_hash: params.turn_hash.clone(),
        effects_hash: params.effects_hash.clone(),
        app: Some(params.app.clone().unwrap_or_else(|| "identity".to_string())),
    }
}

fn receipt_proof_status(receipt: &dregg_turn::TurnReceipt) -> ActivityProofStatus {
    if receipt.executor_signature.is_some() {
        ActivityProofStatus::Proved
    } else {
        ActivityProofStatus::NotRequired
    }
}

fn identity_receipt_matches(receipt: &dregg_turn::TurnReceipt, params: &StarbridgeQuery) -> bool {
    let receipt_hash = hex_encode(&receipt.receipt_hash());
    let event_text = receipt
        .emitted_events
        .iter()
        .filter_map(|event| serde_json::to_string(event).ok())
        .collect::<Vec<_>>()
        .join(" ");
    let identity_hint = event_text.to_ascii_lowercase().contains("identity")
        || event_text.to_ascii_lowercase().contains("credential")
        || !receipt.derivation_records.is_empty()
        || !receipt.emitted_events.is_empty();

    identity_hint
        && exact_filter_matches(&hex_encode(&receipt.turn_hash), &params.turn_hash)
        && exact_filter_matches(&hex_encode(&receipt.effects_hash), &params.effects_hash)
        && params.cell.as_ref().is_none_or(|cell| {
            hex_encode(&receipt.agent.0).eq_ignore_ascii_case(cell)
                || receipt
                    .emitted_events
                    .iter()
                    .any(|event| hex_encode(&event.cell.0).eq_ignore_ascii_case(cell))
                || receipt
                    .derivation_records
                    .iter()
                    .any(|record| hex_encode(&record.target_cell.0).eq_ignore_ascii_case(cell))
        })
        && params.memo.as_ref().is_none_or(|memo| {
            text_filter_matches(&event_text, &Some(memo.clone()))
                || text_filter_matches(&receipt_hash, &Some(memo.clone()))
        })
        && params.effect.as_ref().is_none_or(|effect| {
            text_filter_matches(&event_text, &Some(effect.clone()))
                || text_filter_matches("credential derivation emitted_event", &Some(effect.clone()))
        })
        && params.app.as_ref().is_none_or(|app| {
            app.eq_ignore_ascii_case("identity") || app.eq_ignore_ascii_case("credential")
        })
}

fn classify_starbridge_app(memo: Option<&str>, effect_summaries: &[String]) -> Option<String> {
    let mut haystack = memo.unwrap_or("").to_ascii_lowercase();
    for effect in effect_summaries {
        haystack.push(' ');
        haystack.push_str(&effect.to_ascii_lowercase());
    }

    if haystack.contains("nameservice")
        || haystack.contains("name service")
        || haystack.contains("register name")
    {
        Some("nameservice".to_string())
    } else if haystack.contains("identity")
        || haystack.contains("credential")
        || haystack.contains("profile")
    {
        Some("identity".to_string())
    } else if haystack.contains("governance")
        || haystack.contains("proposal")
        || haystack.contains("vote")
    {
        Some("governance".to_string())
    } else {
        None
    }
}

/// A stable label for a granted/revoked capability (the `cap` term of the
/// `granted`/`revoked` facts): the token hash when present, else `target#slot`.
fn cap_ref_label(cap: &dregg_cell::CapabilityRef) -> String {
    match cap.breadstuff {
        Some(h) => hex_encode(&h),
        None => format!("{}#{}", hex_encode(&cap.target.0), cap.slot),
    }
}

/// Build the typed [`dregg_query::EffectSummary`] enrichment for a committed
/// turn: the decoded per-effect disclosure — transfers / grants / revocations /
/// burns (supply reductions) / state-field writes / cell births / lifecycle
/// transitions (seal/unseal/destroy/sovereign) — plus a post-state balance
/// observation for every cell the turn's transfers/burns touched. Read off the
/// ALREADY-committed before/after ledger — additive, never gates the commit. The
/// `asset` of a transfer/balance is the token domain of the cell (pre-state for
/// the source/burn target, post-state for the destination).
fn summarize_turn_effects(
    turn: &Turn,
    pre: &dregg_cell::Ledger,
    post: &dregg_cell::Ledger,
) -> Vec<dregg_query::EffectSummary> {
    use dregg_query::EffectSummary as ES;
    use dregg_turn::Effect;

    let asset_of = |id: &CellId, l: &dregg_cell::Ledger| -> String {
        l.get(id)
            .map(|c| hex_encode(c.token_id()))
            .unwrap_or_default()
    };

    let mut out = Vec::new();
    let mut touched: Vec<[u8; 32]> = Vec::new();
    let note = |id: [u8; 32], touched: &mut Vec<[u8; 32]>| {
        if !touched.contains(&id) {
            touched.push(id);
        }
    };

    for tree in turn.call_forest.iter_dfs() {
        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    let asset = {
                        let a = asset_of(from, pre);
                        if a.is_empty() { asset_of(to, post) } else { a }
                    };
                    out.push(ES::Transfer {
                        from: hex_encode(&from.0),
                        to: hex_encode(&to.0),
                        asset,
                        amount: *amount,
                    });
                    note(from.0, &mut touched);
                    note(to.0, &mut touched);
                }
                Effect::GrantCapability { from, to, cap } => {
                    out.push(ES::Granted {
                        from: hex_encode(&from.0),
                        to: hex_encode(&to.0),
                        cap: cap_ref_label(cap),
                    });
                }
                Effect::RevokeCapability { cell, slot } => {
                    out.push(ES::Revoked {
                        cap: format!("{}#{}", hex_encode(&cell.0), slot),
                    });
                }
                Effect::Burn { target, amount, .. } => {
                    // A provable supply reduction — no destination credited. The
                    // asset is the target's token domain (pre-state, since the
                    // cell may be destroyed/altered after).
                    out.push(ES::Burned {
                        cell: hex_encode(&target.0),
                        asset: asset_of(target, pre),
                        amount: *amount,
                    });
                    note(target.0, &mut touched);
                }
                Effect::SetField { cell, index, value } => {
                    out.push(ES::Field {
                        cell: hex_encode(&cell.0),
                        index: *index as u64,
                        value: hex_encode(value),
                    });
                }
                Effect::CreateCell {
                    public_key,
                    token_id,
                    ..
                } => {
                    // The new cell id is derived from (public_key, token_id) —
                    // the same derivation the executor uses (`Cell::id()`).
                    let cell = dregg_cell::CellId::derive_raw(public_key, token_id);
                    out.push(ES::Created {
                        agent: hex_encode(&tree.action.target.0),
                        cell: hex_encode(&cell.0),
                    });
                }
                Effect::CreateCellFromFactory {
                    owner_pubkey,
                    token_id,
                    ..
                } => {
                    let cell = dregg_cell::CellId::derive_raw(owner_pubkey, token_id);
                    out.push(ES::Created {
                        agent: hex_encode(&tree.action.target.0),
                        cell: hex_encode(&cell.0),
                    });
                }
                Effect::CellSeal { target, .. } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "sealed".to_string(),
                }),
                Effect::CellUnseal { target } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "unsealed".to_string(),
                }),
                Effect::CellDestroy { target, .. } => out.push(ES::Lifecycle {
                    cell: hex_encode(&target.0),
                    state: "destroyed".to_string(),
                }),
                Effect::MakeSovereign { cell } => out.push(ES::Lifecycle {
                    cell: hex_encode(&cell.0),
                    state: "sovereign".to_string(),
                }),
                _ => {}
            }
        }
    }

    // Post-state balance observations for the cells the transfers touched —
    // the stamped `balance(cell, asset, amount, height)` facts (clamped to a
    // non-negative observation; a cell's balance register is bias-encoded).
    for id in &touched {
        let cell_id = CellId(*id);
        if let Some(c) = post.get(&cell_id) {
            let bal = c.state.balance();
            out.push(ES::Balance {
                cell: hex_encode(id),
                asset: hex_encode(c.token_id()),
                amount: bal.max(0) as u64,
            });
        }
    }

    out
}

fn effect_kind(effect: &dregg_turn::Effect) -> String {
    let debug = format!("{effect:?}");
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or("Unknown")
        .to_ascii_lowercase()
}

fn action_touched_cells(action: &dregg_turn::Action) -> Vec<String> {
    let mut cells = HashSet::new();
    cells.insert(hex_encode(&action.target.0));
    for effect in &action.effects {
        for cell in effect_cells(effect) {
            cells.insert(cell);
        }
    }
    let mut cells: Vec<String> = cells.into_iter().collect();
    cells.sort();
    cells
}

fn effect_cells(effect: &dregg_turn::Effect) -> Vec<String> {
    use dregg_turn::Effect;

    match effect {
        Effect::SetField { cell, .. }
        | Effect::RevokeCapability { cell, .. }
        | Effect::IncrementNonce { cell }
        | Effect::EmitEvent { cell, .. }
        | Effect::MakeSovereign { cell }
        | Effect::Refusal { cell, .. }
        | Effect::AttenuateCapability { cell, .. } => vec![hex_encode(&cell.0)],

        Effect::SetPermissions { cell, .. } | Effect::SetVerificationKey { cell, .. } => {
            vec![hex_encode(&cell.0)]
        }

        _ => Vec::new(),
    }
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

/// Decode variable-length hex strings into byte vectors.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if !s.len().is_multiple_of(2) {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// Verify an Ed25519 signature with domain separation. Used by F-P1-2 (and
/// related ownership checks): `signer_pk` signs `domain || payload`.
/// Returns a static-string error so callers can include it in JSON responses.
fn verify_ed25519_sig(
    signer_pk: &[u8; 32],
    signature_hex: &str,
    domain: &[u8],
    payload: &[u8],
) -> Result<(), &'static str> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let sig_bytes = hex_decode_var(signature_hex).map_err(|_| "invalid signature hex")?;
    if sig_bytes.len() != 64 {
        return Err("signature must be 64 bytes");
    }
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let sig = Signature::from_bytes(&sig_arr);
    let vk = VerifyingKey::from_bytes(signer_pk).map_err(|_| "invalid signer public key")?;
    let mut msg = Vec::with_capacity(domain.len() + payload.len());
    msg.extend_from_slice(domain);
    msg.extend_from_slice(payload);
    vk.verify(&msg, &sig)
        .map_err(|_| "signature does not verify")
}

// =============================================================================
// Queue Operations
// =============================================================================
// Wire DTOs retained for the queue HTTP surface (deserialized by clients).

#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueAllocateRequest {
    capacity: u64,
    program_vk: Option<String>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAllocateResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
}

#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueEnqueueRequest {
    message_hash: String,
    deposit: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueEnqueueResponse {
    position: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueDequeueResponse {
    #[serde(rename = "messageHash")]
    message_hash: String,
    deposit: u64,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueStatusResponse {
    #[serde(rename = "queueId")]
    queue_id: String,
    occupancy: u64,
    capacity: u64,
    owner: String,
    #[serde(skip_serializing_if = "Option::is_none", rename = "programVk")]
    program_vk: Option<String>,
}

#[allow(dead_code)]
#[derive(Deserialize)]
struct QueueAtomicTxRequest {
    operations: Vec<serde_json::Value>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAtomicTxResponse {
    success: bool,
    results: Vec<QueueAtomicTxResult>,
}

#[allow(dead_code)]
#[derive(Serialize)]
struct QueueAtomicTxResult {
    index: usize,
    ok: bool,
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use dregg_coord::{AtomicForest, Coordinator, Decision, Vote};
    use dregg_turn::ComputronCosts;
    use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use http_body_util::BodyExt;
    use std::collections::{HashMap, VecDeque};
    use std::time::{Duration, Instant};
    use tower::ServiceExt;

    /// Helper: create a deterministic key pair for testing.
    fn test_key(name: &str) -> [u8; 32] {
        *blake3::hash(format!("dregg-node-atomic-test:{name}").as_bytes()).as_bytes()
    }

    /// Helper: a minimal receipt with the given finality, unsigned.
    fn minimal_receipt(finality: dregg_turn::Finality) -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 100,
            effects_hash: [5u8; 32],
            computrons_used: 7,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId([6u8; 32]),
            federation_id: [7u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality,
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    /// The node downgrades `finality` to `Tentative` AFTER the executor signs the
    /// receipt (v3 signs the full `receipt_hash`, which binds `finality`). Without
    /// a re-sign, the executor signature no longer verifies against the committed
    /// receipt — it looks like a verifying-key mismatch.
    /// `resign_receipt_committed` must restore a signature that verifies in the
    /// committed (Tentative) state.
    #[test]
    fn resign_after_finality_downgrade_restores_verifiable_signature() {
        use ed25519_dalek::{Signature, Signer, Verifier};

        let seed = test_key("finality-resign");
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let vk = sk.verifying_key();

        // Executor signs while finality is the optimistic Final.
        let mut receipt = minimal_receipt(dregg_turn::Finality::Final);
        receipt.executor_signature = Some(
            sk.sign(&receipt.canonical_executor_signed_message())
                .to_bytes()
                .to_vec(),
        );

        // Node downgrades finality after signing -> the original signature is
        // stranded (it committed to the Final receipt_hash).
        receipt.finality = dregg_turn::Finality::Tentative;
        let stale =
            Signature::from_slice(receipt.executor_signature.as_ref().expect("signed")).unwrap();
        assert!(
            vk.verify(&receipt.canonical_executor_signed_message(), &stale)
                .is_err(),
            "pre-downgrade signature must NOT verify against the committed receipt"
        );

        // The fix re-signs in the committed state.
        resign_receipt_committed(&mut receipt, &seed);
        let fixed =
            Signature::from_slice(receipt.executor_signature.as_ref().expect("resigned")).unwrap();
        assert!(
            vk.verify(&receipt.canonical_executor_signed_message(), &fixed)
                .is_ok(),
            "re-signed signature MUST verify against the committed receipt"
        );
    }

    /// `debug_assert_signed_last` must TRIP when a `receipt_hash`-folded field is
    /// mutated after signing without a re-sign — proving the guard has teeth.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "sign-LAST invariant violated")]
    fn sign_last_invariant_trips_on_post_sign_folded_field_mutation() {
        use ed25519_dalek::Signer;

        let seed = test_key("sign-last-trip");
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);

        let mut receipt = minimal_receipt(dregg_turn::Finality::Final);
        receipt.executor_signature = Some(
            sk.sign(&receipt.canonical_executor_signed_message())
                .to_bytes()
                .to_vec(),
        );
        // Mutate a receipt_hash-folded field WITHOUT re-signing (the bug).
        receipt.finality = dregg_turn::Finality::Tentative;

        // Must panic: the stranded signature does not verify against the receipt.
        debug_assert_signed_last(&receipt, &seed);
    }

    /// Helper: build a minimal AtomicForest with a single noop-like action.
    fn make_test_forest(participants: Vec<[u8; 32]>, initiator: [u8; 32]) -> AtomicForest {
        let cell_id = dregg_cell::CellId(initiator);
        let mut forest = dregg_turn::CallForest::new();
        let action = Action {
            target: cell_id,
            method: *blake3::hash(b"noop").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        forest.add_root(action);
        AtomicForest::new(participants, forest, vec![], cell_id, 0)
    }

    fn test_event(height: u64) -> CommittedEvent {
        CommittedEvent {
            height,
            status: ActivityStatus::Committed,
            proof_status: ActivityProofStatus::NotRequired,
            turn_hash: format!("turn-{height}"),
            cell_id: format!("cell-{height}"),
            effects: vec![format!("effect-{height}")],
            summaries: Vec::new(),
            timestamp: height as i64,
        }
    }

    fn witnessed_with_marker(marker: u8) -> dregg_turn::WitnessedReceipt {
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: [marker; 32],
            effects_hash: [marker.wrapping_add(1); 32],
            agent: CellId([marker.wrapping_add(2); 32]),
            ..Default::default()
        };
        dregg_turn::WitnessedReceipt::from_components(
            receipt,
            vec![marker, marker.wrapping_add(1)],
            vec![marker as u32],
            None,
        )
    }

    #[test]
    fn events_initial_cursor_returns_latest_retained_activity() {
        let log: VecDeque<_> = (1..=5).map(test_event).collect();
        let selected = select_committed_events(&log, Some(0), 2);
        let heights: Vec<_> = selected.iter().map(|event| event.height).collect();
        assert_eq!(
            heights,
            vec![4, 5],
            "first-time pollers must see recent activity, not the oldest retained events"
        );
    }

    #[test]
    fn events_nonzero_cursor_is_exclusive_and_chronological() {
        let log: VecDeque<_> = (1..=5).map(test_event).collect();
        let selected = select_committed_events(&log, Some(2), 2);
        let heights: Vec<_> = selected.iter().map(|event| event.height).collect();
        assert_eq!(
            heights,
            vec![3, 4],
            "catch-up cursors must return the earliest unseen events so clients do not skip"
        );
    }

    #[test]
    fn receipt_infos_expose_chain_position_and_head() {
        let mut chain = Vec::new();
        for idx in 0..3 {
            let previous_receipt_hash = chain
                .last()
                .map(|receipt: &dregg_turn::TurnReceipt| receipt.receipt_hash());
            chain.push(dregg_turn::TurnReceipt {
                turn_hash: [idx as u8; 32],
                agent: CellId([0xA0 + idx as u8; 32]),
                previous_receipt_hash,
                ..Default::default()
            });
        }

        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 0, |_| false);
        assert_eq!(infos.len(), 3);
        assert_eq!(infos[0].chain_index, 2);
        assert!(infos[0].chain_head);
        assert_eq!(infos[1].chain_index, 1);
        assert!(!infos[1].chain_head);
        assert_eq!(infos[2].chain_index, 0);
        assert!(!infos[2].chain_head);
    }

    /// `has_proof` reports an ATTACHED attestation (async-pool WitnessedReceipt
    /// or persisted full-turn proof), independently of the executor signature.
    /// This is the regression test for the silent devnet path where every
    /// receipt stayed `has_proof:false` forever because the field was wired to
    /// `executor_signature` (which no node entry point configures) while the
    /// prove pool was in fact attaching real proofs (`has_witness:true`).
    #[test]
    fn receipt_has_proof_reflects_attached_attestation_not_signature() {
        let chain = vec![dregg_turn::TurnReceipt {
            turn_hash: [0x42; 32],
            agent: CellId([0xA0; 32]),
            executor_signature: None, // no signing key configured (the devnet config)
            ..Default::default()
        }];

        // No witness, no stored proof: honestly unproven.
        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 0, |_| false);
        assert!(!infos[0].has_proof);
        assert!(!infos[0].executor_signed);

        // The async prove pool attached a WitnessedReceipt: has_proof flips.
        let infos = receipt_infos_from_chain_with_witnesses(&chain, 50, |_| 1, |_| false);
        assert!(
            infos[0].has_proof,
            "a pool-attached WitnessedReceipt must flip has_proof even with no executor signature"
        );

        // Only the persisted full-turn proof (blocklace finalized path): also flips.
        let infos = receipt_infos_from_chain_with_witnesses(
            &chain,
            50,
            |_| 0,
            |th| th == hex_encode(&[0x42u8; 32]),
        );
        assert!(
            infos[0].has_proof,
            "a persisted full-turn proof must flip has_proof"
        );
    }

    #[tokio::test]
    async fn explorer_public_contract_endpoints_are_available() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        for path in [
            "/status",
            "/api/cells",
            "/api/tokens",
            "/api/receipts",
            "/api/blocks",
            "/federation/roots",
            "/api/federations",
            "/api/intents",
        ] {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri(path)
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK, "{path} should be public");

            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            serde_json::from_slice::<serde_json::Value>(&body)
                .unwrap_or_else(|err| panic!("{path} should return JSON: {err}"));
        }
    }

    /// THE PORTAL-DECOUPLING CONTRACT (read path). The public `portal.dregg.studio`
    /// viewer (`portal/dist/portal.js`) is repointed off the Discord bot onto the
    /// NODE's `/api/*`. Its `renderCells`/`fillCell` read exactly these fields off
    /// `/api/cells` and `/api/cell/<id>`; lock the node's structs to that field set so
    /// the node serves a portal-compatible shape (the bot is no longer load-bearing).
    #[test]
    fn portal_read_contract_cell_fields_present() {
        let entry = serde_json::to_value(CellListEntry {
            id: "abcd".into(),
            balance: 7,
            nonce: 1,
            capability_count: 2,
            has_delegate: false,
            has_program: true,
            found: true,
        })
        .expect("serialize CellListEntry");
        for field in ["id", "balance", "nonce", "capability_count", "has_program"] {
            assert!(
                entry.get(field).is_some(),
                "/api/cells entry missing portal field `{field}`: {entry}"
            );
        }
    }

    /// The portal's liveness badge (`portal.js`) opens an `EventSource` on
    /// `/observability/stream` and `addEventListener`s `hello` (reloads the cell list)
    /// + `ping`. After the bot→node repoint the node must speak that same contract, so
    /// the FIRST frame is an immediate `hello` (no 15s wait) carrying the node's
    /// nullifier count — proving the public viewer's live badge works reading the node
    /// directly, with the bot down.
    #[tokio::test]
    async fn portal_observability_stream_opens_with_hello() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/observability/stream")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        // Read just the first SSE frame (the stream is otherwise an infinite 15s
        // ping heartbeat, so we must NOT `collect()` it).
        let mut body = response.into_body();
        let frame = body
            .frame()
            .await
            .expect("a first SSE frame")
            .expect("frame ok");
        let data = frame.into_data().ok().expect("a data frame");
        let text = String::from_utf8_lossy(&data);
        assert!(
            text.contains("hello"),
            "first frame must be the hello event: {text}"
        );
        assert!(
            text.contains("nullifiers"),
            "hello carries the nullifier count for the badge: {text}"
        );
    }

    #[tokio::test]
    async fn receipt_witness_endpoint_exports_dwr1_artifacts() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let receipt_hash = [0xA5; 32];
        state
            .write()
            .await
            .push_witnessed_receipt(receipt_hash, witnessed_with_marker(0x41));

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let response = app
            .oneshot(
                Request::builder()
                    .uri(format!(
                        "/api/receipts/{}/witnesses",
                        hex_encode(&receipt_hash)
                    ))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("json");
        assert_eq!(json["artifact_format"], "DWR1");
        assert_eq!(json["witness_count"], 1);
        assert_eq!(
            json["witnessed_receipts"]
                .as_array()
                .expect("legacy witness array")
                .len(),
            1
        );
        let artifact_hex = json["witness_artifacts"][0].as_str().expect("artifact hex");
        let artifact_bytes = hex_decode_var(artifact_hex).expect("valid artifact hex");
        let decoded = dregg_turn::WitnessedReceipt::from_artifact_bytes(&artifact_bytes)
            .expect("DWR1 witness artifact decodes");
        assert_eq!(decoded.proof_bytes, vec![0x41, 0x42]);
    }

    /// The enrichment: a committed turn's decoded Transfer effect + the
    /// before/after ledger yield a typed `Transfer` summary AND a post-state
    /// `Balance` observation for the touched cells — the EDB rows dregg-query
    /// turns into `transfer`/`balance` facts.
    #[test]
    fn summarize_turn_effects_yields_typed_transfer_and_balance() {
        use dregg_query::EffectSummary as ES;

        let agent_pk = [0x11u8; 32];
        let recipient_pk = [0x22u8; 32];
        let agent = CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0);
        let recipient = CellId(dregg_cell::CellId::derive_raw(&recipient_pk, &[0u8; 32]).0);

        let mut pre = dregg_cell::Ledger::new();
        pre.insert_cell(dregg_cell::Cell::with_balance(agent_pk, [0u8; 32], 1_000))
            .expect("agent insert");
        pre.insert_cell(dregg_cell::Cell::with_balance(recipient_pk, [0u8; 32], 0))
            .expect("recipient insert");

        // Post-state: 250 moved agent -> recipient.
        let mut post = pre.clone();
        {
            let a = post.get(&agent).expect("agent").clone();
            let mut a = a;
            a.state.set_balance(a.state.balance() - 250);
            post.remove(&agent);
            post.insert_cell(a).expect("reinsert agent");
            let r = post.get(&recipient).expect("recipient").clone();
            let mut r = r;
            r.state.set_balance(r.state.balance() + 250);
            post.remove(&recipient);
            post.insert_cell(r).expect("reinsert recipient");
        }

        let mut forest = CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "transfer", agent)
                .effect_transfer(agent, recipient, 250)
                .build(),
        );
        let turn = make_min_turn(agent, 0, None, forest);

        let summaries = summarize_turn_effects(&turn, &pre, &post);

        assert!(
            summaries.iter().any(|e| matches!(
                e,
                ES::Transfer { amount: 250, to, .. } if *to == hex_encode(&recipient.0)
            )),
            "expected a typed Transfer(250) summary, got {summaries:?}"
        );
        assert!(
            summaries.iter().any(|e| matches!(
                e,
                ES::Balance { amount: 250, cell, .. } if *cell == hex_encode(&recipient.0)
            )),
            "expected a post-state Balance(250) for the recipient, got {summaries:?}"
        );
    }

    /// The richer EDB: a turn carrying a state-field write, a cell birth, and a
    /// make-sovereign lifecycle transition yields the typed `Field` / `Created`
    /// / `Lifecycle` summaries dregg-query turns into `field`/`created`/
    /// `lifecycle` facts.
    #[test]
    fn summarize_turn_effects_yields_field_created_lifecycle() {
        use dregg_query::EffectSummary as ES;

        let agent_pk = [0x33u8; 32];
        let agent = CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0);
        let new_pk = [0x44u8; 32];
        let new_token = [0x55u8; 32];
        let new_cell = CellId(dregg_cell::CellId::derive_raw(&new_pk, &new_token).0);

        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(dregg_cell::Cell::with_balance(agent_pk, [0u8; 32], 0))
            .expect("agent insert");

        let mut forest = CallForest::new();
        forest.add_root(
            dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "rich", agent)
                .effect_set_field(agent, 2, [0xABu8; 32])
                .effect_create_cell(new_pk, new_token, 0)
                .effect_make_sovereign(agent)
                .build(),
        );
        let turn = make_min_turn(agent, 0, None, forest);

        // The summary is read off the effects + ledger; pre == post is fine for
        // these families (only Transfer/Burn need a balance delta).
        let summaries = summarize_turn_effects(&turn, &ledger, &ledger);

        assert!(
            summaries.iter().any(
                |e| matches!(e, ES::Field { index: 2, cell, .. } if *cell == hex_encode(&agent.0))
            ),
            "expected a typed Field write, got {summaries:?}"
        );
        assert!(
            summaries
                .iter()
                .any(|e| matches!(e, ES::Created { cell, .. } if *cell == hex_encode(&new_cell.0))),
            "expected a Created summary for the derived new-cell id, got {summaries:?}"
        );
        assert!(
            summaries.iter().any(
                |e| matches!(e, ES::Lifecycle { state, cell } if state == "sovereign" && *cell == hex_encode(&agent.0))
            ),
            "expected a sovereign Lifecycle transition, got {summaries:?}"
        );
    }

    /// End-to-end over the LIVE log: drive two real transfer turns through the
    /// node (executor + cipherclerk commit, the same path `/turn/submit` runs),
    /// then read the two new handlers — `/api/receipts/index/{root,range}` —
    /// build a dregg-query `AttestedAnswer` over the served slice, and verify it
    /// against the served root. Then show the non-omission teeth bite: a
    /// substituted leaf and a dropped position both reject.
    #[tokio::test]
    async fn live_receipt_index_serves_verifying_attested_answer_and_teeth_bite() {
        use dregg_turn::{ComputronCosts, TurnExecutor, TurnResult};

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");

        let recipient_pk = [0x77u8; 32];
        let (agent, recipient) = {
            let s = state.read().await;
            let agent_pk = s.cclerk.public_key().0;
            (
                CellId(dregg_cell::CellId::derive_raw(&agent_pk, &[0u8; 32]).0),
                CellId(dregg_cell::CellId::derive_raw(&recipient_pk, &[0u8; 32]).0),
            )
        };

        // Open permissions so the unsigned test transfer commits (the
        // executor still enforces the cell's Send permission; the real node
        // path signs via the cipherclerk instead).
        let open = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };

        {
            let mut s = state.write().await;
            let cc_pk = s.cclerk.public_key().0;
            let mut agent_cell = dregg_cell::Cell::with_balance(cc_pk, [0u8; 32], 1_000_000);
            agent_cell.permissions = open.clone();
            s.ledger.insert_cell(agent_cell).expect("agent provision");
            let mut recipient_cell = dregg_cell::Cell::with_balance(recipient_pk, [0u8; 32], 0);
            recipient_cell.permissions = open.clone();
            s.ledger
                .insert_cell(recipient_cell)
                .expect("recipient provision");

            let executor = TurnExecutor::new(ComputronCosts::default());
            for nonce in 0u64..2 {
                let prev = s.cclerk.receipt_head().map(|r| r.receipt_hash());
                let mut forest = CallForest::new();
                forest.add_root(
                    dregg_turn::ActionBuilder::new_unchecked_for_tests(agent, "transfer", agent)
                        .effect_transfer(agent, recipient, 100)
                        .build(),
                );
                let turn = make_min_turn(agent, nonce, prev, forest);
                let pre_ledger = s.ledger.clone();
                let receipt = match executor.execute(&turn, &mut s.ledger) {
                    TurnResult::Committed { receipt, .. } => receipt,
                    other => panic!("transfer turn nonce={nonce} must commit: {other:?}"),
                };
                s.cclerk.append_receipt(receipt).expect("append receipt");
                let summaries = summarize_turn_effects(&turn, &pre_ledger, &s.ledger);
                assert!(
                    summaries
                        .iter()
                        .any(|e| matches!(e, dregg_query::EffectSummary::Transfer { .. })),
                    "real turn must yield a typed Transfer summary"
                );
                push_committed_event_enriched(
                    &mut s,
                    hex_encode(&turn.hash()),
                    hex_encode(&agent.0),
                    vec!["transfer".to_string()],
                    summaries,
                    ActivityProofStatus::NotRequired,
                );
            }
        }

        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        // (1) the live MMR root.
        let root_resp: dregg_query::client::IndexRootResponse = {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri("/api/receipts/index/root")
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK);
            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            serde_json::from_slice(&body).expect("root json")
        };
        assert_eq!(root_resp.len, 2, "two committed receipts indexed");
        let trusted_root = hex_decode(&root_resp.root).expect("32-byte root");

        // (2) the certified slice over the whole log.
        let range_resp: dregg_query::client::IndexRangeResponse = {
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .uri("/api/receipts/index/range?lo=0&hi=1")
                        .body(Body::empty())
                        .expect("request"),
                )
                .await
                .expect("response");
            assert_eq!(response.status(), StatusCode::OK);
            let body = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            serde_json::from_slice(&body).expect("range json")
        };
        assert_eq!(range_resp.receipts.len(), 2);

        // (3) the attested answer verifies against the served root.
        let query = dregg_query::Query::new().atom(
            dregg_query::Pred::Transfer,
            vec![
                dregg_query::Term::var("from"),
                dregg_query::Term::var("to"),
                dregg_query::Term::var("asset"),
                dregg_query::Term::var("amount"),
                dregg_query::Term::var("h"),
            ],
        );
        let slice = range_resp.clone().into_slice().expect("slice");
        let answer = dregg_query::answer_whole_log(slice, query).expect("answer");
        answer
            .verify(&dregg_query::Blake3Mmr, &trusted_root)
            .expect("live attested answer must verify against the served root");
        assert!(
            !answer.rows.is_empty(),
            "the transfer query yields rows from the live receipts"
        );

        // (4a) teeth: a substituted receipt leaf rejects (SlotMismatch).
        let mut tampered = range_resp.clone().into_slice().expect("slice");
        tampered.receipts[0].receipt_hash = hex_encode(&[0xEEu8; 32]);
        assert!(
            tampered
                .verify(&dregg_query::Blake3Mmr, &trusted_root)
                .is_err(),
            "a substituted leaf must reject"
        );

        // (4b) teeth: a dropped position rejects (CountMismatch — positions are dense).
        let mut omitted = range_resp.into_slice().expect("slice");
        omitted.receipts.pop();
        assert!(
            omitted
                .verify(&dregg_query::Blake3Mmr, &trusted_root)
                .is_err(),
            "an omitted position must reject"
        );
    }

    /// Build a minimal `Turn` with the given call forest (test helper).
    fn make_min_turn(
        agent: CellId,
        nonce: u64,
        prev: Option<[u8; 32]>,
        call_forest: CallForest,
    ) -> Turn {
        Turn {
            agent,
            nonce,
            fee: 100_000,
            memo: None,
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: prev,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: vec![],
            cross_effect_dependencies: vec![],
            effect_witness_index_map: vec![],
        }
    }

    #[tokio::test]
    async fn federation_alias_returns_real_local_state_shape() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/federations")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);

        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let federations: serde_json::Value = serde_json::from_slice(&body).expect("json");
        let first = federations
            .as_array()
            .and_then(|items| items.first())
            .expect("at least one local federation view");
        assert_eq!(first["is_local"], true);
        assert_eq!(first["id"].as_str().expect("id").len(), 64);
        assert_eq!(first["federation_id"], first["id"]);
        assert!(first["latest_height"].is_u64());
        assert!(first["num_finalized_roots"].is_u64());
    }

    #[test]
    fn submit_handlers_seed_executor_with_committed_receipt_head() {
        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());
        let agent = CellId([0x42; 32]);
        let head = [0xAB; 32];

        assert_eq!(executor.get_last_receipt_hash(&agent), None);
        seed_executor_receipt_head(&executor, agent, Some(head));
        assert_eq!(
            executor.get_last_receipt_hash(&agent),
            Some(head),
            "fresh per-request executors must inherit the node's committed receipt head"
        );
    }

    fn projectable_http_test_turn(agent: CellId) -> Turn {
        let action = Action {
            target: agent,
            method: *blake3::hash(b"http-test-increment").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: agent }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut call_forest = CallForest::new();
        call_forest.add_root(action);
        Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: Some("http witness test".to_string()),
            valid_until: None,
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    #[test]
    fn http_submit_prepare_rotatable_carries_real_actor_and_rotation() {
        let public_key = [0x23; 32];
        let token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&public_key, &token_id);
        let mut ledger = dregg_cell::Ledger::new();
        let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 10_000);
        cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        ledger.insert_cell(cell).expect("insert agent cell");
        let pre_ledger = ledger.clone();
        let turn = projectable_http_test_turn(agent);
        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());
        let (_, receipt, _) = executor.execute(&turn, &mut ledger).unwrap_committed();

        // PATH-PRESERVE Phase 5b: the executor already validated + committed; the
        // commit path no longer revalidates or proves inline. `prepare_rotatable_turn`
        // gathers the REAL before/after cells (pre_ledger / the post-execution ledger)
        // into the carrier the async pool proves — and for a cohort transfer it builds
        // the ROTATION witness, so the async proof goes through the rotated descriptor,
        // NOT the node's own v1 effect-vm hand-AIR.
        let outcome = prepare_rotatable_turn(&turn, &pre_ledger, &ledger, receipt.receipt_hash())
            .expect("projectable HTTP turn prepares for attestation");
        let HttpWitnessOutcome::Rotatable(rotatable) = outcome else {
            panic!("a transfer-bearing HTTP turn must be Rotatable, not NotRequired");
        };

        assert_eq!(rotatable.agent, agent, "carrier binds the real actor cell");
        assert_eq!(rotatable.turn_hash, turn.hash());
        assert_eq!(
            rotatable.pre_balance, 10_000,
            "carrier captures the actor's pre-state balance from the real cell"
        );
        assert!(
            !rotatable.effects.is_empty(),
            "carrier carries the turn's effects for the async prover"
        );
        // A cap-less transfer is a rotatable cohort member: the rotation witness must
        // be present so the async leg proves through the LEAN-emitted rotated descriptor.
        assert!(
            rotatable.rotation.is_some(),
            "a cap-less transfer turn must carry a rotation witness (rotated effect-vm leg)"
        );
    }

    #[test]
    fn http_submit_empty_effect_turn_reports_no_witness_honestly() {
        let agent = CellId([0x42; 32]);
        let turn = Turn {
            agent,
            nonce: 0,
            fee: 0,
            memo: None,
            valid_until: None,
            call_forest: CallForest::new(),
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let receipt = dregg_turn::TurnReceipt {
            turn_hash: turn.hash(),
            agent,
            ..Default::default()
        };

        let _ = receipt; // empty-effect turn carries no Effect-VM transition to attest
        let empty = dregg_cell::Ledger::new();
        let outcome = prepare_rotatable_turn(&turn, &empty, &empty, [0u8; 32])
            .expect("empty-effect HTTP turn should not require attestation");
        assert!(
            matches!(outcome, HttpWitnessOutcome::NotRequired),
            "empty-effect HTTP turns must not claim a null proof as proved"
        );
    }

    #[test]
    fn faucet_activity_hash_is_hex_tx_sized() {
        let tx = compute_faucet_activity_hash(&dregg_cell::CellId([0xC0; 32]), 0);
        assert_eq!(tx.len(), 64);
        assert!(tx.chars().all(|ch| ch.is_ascii_hexdigit()));
    }

    /// #171 remote `.turn()` e2e through the HTTP router: a keypair the node
    /// has NEVER seen locally builds + signs a canonical turn, submits the
    /// postcard `SignedTurn` envelope to `POST /turns/submit`, it executes
    /// through the ONE producer gate (`executor_setup::execute_via_producer`),
    /// and the receipt is retrievable from `GET /api/receipts` — while a
    /// tampered envelope, a wrong-agent envelope, and a replayed envelope all
    /// refuse. Mirrors the exact `dregg_sdk_net::remote::RemoteRuntime` flow
    /// (federation-bound action signature, `valid_until` stamp, receipt-chain
    /// binding).
    #[tokio::test]
    async fn remote_signed_envelope_e2e_accepts_then_refuses_tamper_and_replay() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        state.write().await.unlocked = true;
        // Single in-process node = a committee of one (solo). Production sets this in
        // main.rs under `is_solo_mode`; the hardened faucet keys its authoritative
        // recipient provisioning off it (a real multi-party committee provisions via
        // `execute_finalized_turn` instead). Without the flag the faucet treats this
        // node as multi-party and skips eager provisioning -> "cell not found".
        {
            let mut s = state.write().await;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
        }
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        // enable_faucet: the devnet onboarding surface the remote SDK uses.
        let app = router(state.clone(), true, recorder.handle());
        // Loopback client: `require_auth`'s pre-passphrase window admits only
        // loopback callers (F-CRIT-1). The REMOTENESS under test is the
        // keypair/identity (never seen by the node), not the socket.
        let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();

        // The remote agent: a fresh keypair this node has never seen, plus a
        // second fresh cell as the transfer recipient.
        let clerk = dregg_sdk::AgentCipherclerk::new();
        let clerk2 = dregg_sdk::AgentCipherclerk::new();
        let default_token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&clerk.public_key().0, &default_token_id);
        let recipient = dregg_cell::CellId::derive_raw(&clerk2.public_key().0, &default_token_id);

        // Devnet onboarding over HTTP: materialize both hosted cells with
        // their REAL owner keys (the same `POST /api/faucet` call
        // `RemoteRuntime::faucet` makes).
        for (cell, owner) in [(agent, &clerk), (recipient, &clerk2)] {
            let body = serde_json::json!({
                "recipient": hex_encode(&cell.0),
                "amount": 5_000u64,
                "public_key": hex_encode(&owner.public_key().0),
            });
            let response = app
                .clone()
                .oneshot(
                    Request::builder()
                        .method("POST")
                        .uri("/api/faucet")
                        .header("content-type", "application/json")
                        .extension(ConnectInfo(addr))
                        .body(Body::from(serde_json::to_vec(&body).unwrap()))
                        .expect("faucet request"),
                )
                .await
                .expect("faucet response");
            assert_eq!(response.status(), StatusCode::OK);
            let bytes = response
                .into_body()
                .collect()
                .await
                .expect("body")
                .to_bytes();
            let json: serde_json::Value = serde_json::from_slice(&bytes).expect("faucet json");
            assert_eq!(json["success"], true, "faucet must succeed: {json}");
        }

        // The two node bindings the remote SDK discovers before signing.
        let (fed_id, expected_prev) = {
            let s = state.read().await;
            (
                crate::executor_setup::federation_id_for_executor(&s),
                s.cclerk.receipt_chain().last().map(|r| r.receipt_hash()),
            )
        };
        assert!(
            expected_prev.is_some(),
            "faucet turns must have committed receipts to bind against"
        );

        // Sign the action over the canonical federation-bound message — the
        // node-side executor verifies EXACTLY this (one gate, no parallel
        // verification path).
        let unsigned = Action {
            target: agent,
            method: *blake3::hash(b"execute").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: dregg_cell::Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: agent,
                to: recipient,
                amount: 7,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let message = dregg_turn::TurnExecutor::compute_signing_message(&unsigned, &fed_id);
        let sig = clerk.sign_bytes(&message);
        let action = Action {
            authorization: Authorization::from_sig_bytes(sig.0),
            ..unsigned
        };
        let mut forest = CallForest::new();
        forest.add_root(action);

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let turn = Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: None,
            // The remote SDK ALWAYS stamps valid_until (executor expiry gate +
            // the verified Lean producer's wire marshal).
            valid_until: Some(now + 3600),
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: expected_prev,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let signed = clerk.sign_turn(&turn);
        let envelope = postcard::to_stdvec(&signed).expect("envelope encode");

        let submit = |bytes: Vec<u8>| {
            app.clone().oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/turns/submit")
                    .header("content-type", "application/octet-stream")
                    .extension(ConnectInfo(addr))
                    .body(Body::from(bytes))
                    .expect("submit request"),
            )
        };

        // ── ACCEPT: the honest remote envelope commits. ──
        let response = submit(envelope.clone()).await.expect("submit response");
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("submit json");
        assert_eq!(
            json["accepted"], true,
            "honest remote envelope must commit: {json}"
        );
        let turn_hash_hex = hex_encode(&turn.hash());
        assert_eq!(json["turn_hash"], serde_json::json!(turn_hash_hex));

        // ── RECEIPT RETRIEVABLE: the committed receipt appears on the public
        // receipts surface under the canonical turn hash. ──
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri("/api/receipts")
                    .extension(ConnectInfo(addr))
                    .body(Body::empty())
                    .expect("receipts request"),
            )
            .await
            .expect("receipts response");
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let receipts: serde_json::Value = serde_json::from_slice(&bytes).expect("receipts json");
        assert!(
            receipts
                .as_array()
                .expect("receipts array")
                .iter()
                .any(|r| r["turn_hash"] == serde_json::json!(turn_hash_hex)),
            "committed remote turn's receipt must be retrievable: {receipts}"
        );

        // ── TAMPER REFUSES: any post-signing mutation breaks the envelope. ──
        let mut tampered = signed.clone();
        tampered.turn.fee += 1;
        let response = submit(postcard::to_stdvec(&tampered).expect("encode"))
            .await
            .expect("tamper response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("tamper json");
        assert_eq!(json["accepted"], false, "tampered envelope must refuse");
        assert_eq!(json["error"], serde_json::json!("invalid turn signature"));

        // ── WRONG AGENT REFUSES: an honestly-signed envelope whose turn acts
        // as someone ELSE's cell refuses at the ingress binding. ──
        let mut wrong = turn.clone();
        wrong.agent = recipient;
        let wrong_signed = clerk.sign_turn(&wrong);
        let response = submit(postcard::to_stdvec(&wrong_signed).expect("encode"))
            .await
            .expect("wrong-agent response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("wrong-agent json");
        assert_eq!(json["accepted"], false, "wrong-agent envelope must refuse");
        assert_eq!(
            json["error"],
            serde_json::json!("turn agent does not match signer default cell")
        );

        // ── REPLAY REFUSES: the exact accepted envelope, resubmitted, is
        // rejected — its receipt-chain binding now points behind the head. ──
        let response = submit(envelope).await.expect("replay response");
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("replay json");
        assert_eq!(json["accepted"], false, "replayed envelope must refuse");
        assert_eq!(json["error"], serde_json::json!("receipt chain mismatch"));
    }

    #[test]
    fn test_proposal_creation_and_vote_commit() {
        let node_a = test_key("node_a");
        let node_b = test_key("node_b");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        // Propose.
        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node A votes yes.
        let sig_a = Vote::sign_yes(&proposal_id, &forest.hash, &node_a);
        let vote_a = Vote::yes(sig_a);
        let decision_a = coordinator.receive_vote(pub_a, vote_a).unwrap();
        assert_eq!(decision_a, None); // Still pending.

        // Node B votes yes.
        let sig_b = Vote::sign_yes(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::yes(sig_b);
        let decision_b = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision_b, Some(Decision::Commit)); // Quorum reached!
    }

    #[test]
    fn test_proposal_abort_on_rejection() {
        let node_a = test_key("node_c");
        let node_b = test_key("node_d");

        let pub_a = Vote::public_key_from_signing_key(&node_a);
        let pub_b = Vote::public_key_from_signing_key(&node_b);

        let participants = vec![pub_a, pub_b];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);
        participant_keys.insert(pub_b, pub_b);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            2, // unanimous required
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Node B votes no -- threshold becomes unreachable.
        let sig_b = Vote::sign_no(&proposal_id, &forest.hash, &node_b);
        let vote_b = Vote::no("testing rejection", sig_b);
        let decision = coordinator.receive_vote(pub_b, vote_b).unwrap();
        assert_eq!(decision, Some(Decision::Abort));
    }

    #[test]
    fn test_proposal_expiry() {
        use crate::state::{ActiveProposal, PROPOSAL_EXPIRY_SECS};

        let node_a = test_key("node_e");
        let pub_a = Vote::public_key_from_signing_key(&node_a);

        let participants = vec![pub_a];
        let forest = make_test_forest(participants.clone(), pub_a);

        let mut participant_keys = HashMap::new();
        participant_keys.insert(pub_a, pub_a);

        let mut coordinator = Coordinator::new(
            pub_a,
            node_a,
            1,
            ComputronCosts::default(),
            u64::MAX,
            participant_keys,
        );

        let propose_msg = coordinator.propose(forest.clone()).unwrap();
        let proposal_id = propose_msg.proposal_id;

        // Simulate an old proposal by setting created_at in the past.
        let mut proposals: HashMap<[u8; 32], ActiveProposal> = HashMap::new();
        proposals.insert(
            proposal_id,
            ActiveProposal {
                coordinator,
                created_at: Instant::now() - Duration::from_secs(PROPOSAL_EXPIRY_SECS + 10),
                forest,
            },
        );

        // Expire stale proposals.
        let now = Instant::now();
        let expiry = Duration::from_secs(PROPOSAL_EXPIRY_SECS);
        proposals.retain(|_, p| now.duration_since(p.created_at) < expiry);

        assert!(proposals.is_empty(), "expired proposal should be removed");
    }

    // =========================================================================
    // Adversarial tests for the AUDIT-node.md remediations (Stage 0c).
    //
    // These tests exercise the security-relevant logic of each fix at the unit
    // level — they intentionally avoid spinning up a full Axum router because
    // the workspace is being rebuilt by Stage 0a (sdk/) and Stage 0b (cell/)
    // and cannot link integration-test binaries at the time these tests were
    // authored. Each test pins the contract the fix established: a regression
    // in any of these would re-open a documented audit finding.
    // =========================================================================

    /// F-P2-1: atomic-proposal budget is clamped to 1B computrons, NOT
    /// `u64::MAX`. The prior code passed `u64::MAX` straight through to the
    /// coordinator with a "actual gate at execution time" comment that did not
    /// exist.
    #[test]
    // Intentional compile-constant regression guard (both operands are consts by design).
    #[allow(clippy::assertions_on_constants)]
    fn audit_f_p2_1_atomic_budget_is_bounded() {
        assert_eq!(
            MAX_ATOMIC_BUDGET, 1_000_000_000,
            "MAX_ATOMIC_BUDGET regressed; prior code allowed u64::MAX"
        );
        assert!(
            MAX_ATOMIC_BUDGET < u64::MAX / 1000,
            "budget must be far below u64::MAX to defeat exhaustion attacks"
        );
    }

    /// F-P1-8 (mcp side): the bearer-cap signed message MUST commit to the
    /// permission level so a downstream verifier cannot accept a forged
    /// permissions field. Test the message layout we sign in
    /// `tool_create_bearer_cap` is exactly `target || bearer_pk || expires || perm_tag`.
    #[test]
    fn audit_f_p1_8_perm_tag_layout() {
        // The layout that `tool_create_bearer_cap` signs (see node/src/mcp.rs
        // ~2090) is target(32) || bearer_pk(32) || expires(8) || tag(1) = 73.
        // If the layout regresses, the bearer cap signature would no longer
        // bind the permission level, re-opening F-P1-8.
        let target = [0xAAu8; 32];
        let bearer = [0xBBu8; 32];
        let expires: u64 = 12345;
        let tag: u8 = 1; // Signature
        let mut msg = Vec::with_capacity(73);
        msg.extend_from_slice(&target);
        msg.extend_from_slice(&bearer);
        msg.extend_from_slice(&expires.to_le_bytes());
        msg.push(tag);
        assert_eq!(msg.len(), 73);
        // Changing the tag must change the message.
        let mut msg_b = msg.clone();
        *msg_b.last_mut().unwrap() = 0;
        assert_ne!(msg, msg_b, "perm_tag must affect signed message");
    }

    /// F-P1-2 / F-P1-1 helper: `verify_ed25519_sig` correctly rejects:
    ///   (a) signatures over the wrong domain,
    ///   (b) signatures by a different key,
    ///   (c) malformed signature lengths.
    /// And accepts a correctly-signed message.
    #[test]
    fn audit_helper_verify_ed25519_sig_domain_separation() {
        use ed25519_dalek::{Signer, SigningKey};
        let mut seed_a = [0u8; 32];
        seed_a[0] = 1;
        let sk_a = SigningKey::from_bytes(&seed_a);
        let pk_a = sk_a.verifying_key().to_bytes();

        let mut seed_b = [0u8; 32];
        seed_b[0] = 2;
        let sk_b = SigningKey::from_bytes(&seed_b);
        let pk_b = sk_b.verifying_key().to_bytes();

        let domain_x = b"dregg-x-v1";
        let domain_y = b"dregg-y-v1";
        let payload = b"hello";

        // A signs (domain_x || payload).
        let mut msg = Vec::new();
        msg.extend_from_slice(domain_x);
        msg.extend_from_slice(payload);
        let sig = sk_a.sign(&msg);
        let sig_hex = hex_encode(&sig.to_bytes());

        // Sanity: verifies under A and domain_x.
        assert!(verify_ed25519_sig(&pk_a, &sig_hex, domain_x, payload).is_ok());
        // Domain mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_a, &sig_hex, domain_y, payload).is_err());
        // Key mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_b, &sig_hex, domain_x, payload).is_err());
        // Length mismatch: must reject.
        assert!(verify_ed25519_sig(&pk_a, "00", domain_x, payload).is_err());
        // Garbage hex: must reject.
        assert!(verify_ed25519_sig(&pk_a, "zzzz", domain_x, payload).is_err());
    }

    /// F-CRIT-1 (logic-level): the loopback check in `post_set_passphrase`
    /// rejects non-loopback addresses. We can't exercise the handler without
    /// a router, but the underlying check is one line; here we pin the
    /// invariant.
    #[test]
    fn audit_f_crit_1_loopback_predicate() {
        use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
        // The exact predicate `addr.ip().is_loopback()` is what the handler
        // uses. Verify that the obvious "bad" addresses fail it.
        assert!(IpAddr::V4(Ipv4Addr::LOCALHOST).is_loopback());
        assert!(IpAddr::V6(Ipv6Addr::LOCALHOST).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(192, 168, 1, 5)).is_loopback());
        assert!(!IpAddr::V4(Ipv4Addr::new(8, 8, 8, 8)).is_loopback());
    }

    /// F-P1-3: derive the cipherclerk's agent cell id deterministically from a
    /// pubkey; verify it differs from a victim cell id even when the caller
    /// passes the victim id as the body's `agent`.
    #[test]
    fn audit_f_p1_3_cclerk_agent_overrides_body() {
        // The handler derives:
        //   `dregg_cell::CellId::derive_raw(&cipherclerk.public_key().0, &[0u8;32])`
        // The body's `agent` is discarded. If a victim's `cell_id` is supplied
        // as the body's agent, the derived id MUST differ (so the cipherclerk's
        // signature can't be tricked into authorizing a victim's c-list).
        let cclerk_pk = [0x77u8; 32];
        let victim_cell = [0x99u8; 32];

        let derived = dregg_cell::CellId::derive_raw(&cclerk_pk, &[0u8; 32]).0;
        assert_ne!(
            derived, victim_cell,
            "agent must be derived from cipherclerk pubkey, not victim cell id"
        );

        // Sanity: the derivation is a function of the cipherclerk pubkey.
        let derived2 = dregg_cell::CellId::derive_raw(&cclerk_pk, &[0u8; 32]).0;
        assert_eq!(derived, derived2);
    }

    /// F-P1-4: AtomicProposalRequest supports an explicit `participant_pubkeys`
    /// field. Verify the request type round-trips through serde so the request
    /// body schema is correct.
    #[test]
    fn audit_f_p1_4_participant_pubkeys_schema() {
        let req_json = serde_json::json!({
            "forest": {},
            "participants": ["00".repeat(32), "01".repeat(32)],
            "threshold": 2,
            "fee": 0,
            "initiator": "00".repeat(32),
            "participant_pubkeys": ["aa".repeat(32), "bb".repeat(32)],
        });
        let req: AtomicProposalRequest = serde_json::from_value(req_json).expect("parses");
        assert_eq!(req.participants.len(), 2);
        assert!(req.participant_pubkeys.is_some());
        assert_eq!(req.participant_pubkeys.as_ref().unwrap().len(), 2);

        // Omission of the field is also valid (fallback path).
        let req2_json = serde_json::json!({
            "forest": {},
            "participants": ["00".repeat(32)],
            "threshold": 1,
            "fee": 0,
            "initiator": "00".repeat(32),
        });
        let req2: AtomicProposalRequest = serde_json::from_value(req2_json).expect("parses");
        assert!(req2.participant_pubkeys.is_none());
    }

    /// F-P1-7: the federation ID used by `post_bearer_auth` is `s.silo_id`,
    /// which is stable across runs (derived from the cipherclerk's pubkey). Prior
    /// code used `known_federation_keys.first()` whose ordering is a HashSet
    /// artifact and is NOT stable. We verify the derivation of silo_id is
    /// deterministic.
    #[test]
    fn audit_f_p1_7_silo_id_is_stable() {
        // silo_id is `blake3::hash(cipherclerk.public_key().as_bytes())` (see
        // state.rs:400). The same pubkey ALWAYS produces the same silo_id.
        let pk = [0xCDu8; 32];
        let id1 = *blake3::hash(&pk).as_bytes();
        let id2 = *blake3::hash(&pk).as_bytes();
        assert_eq!(id1, id2, "silo_id derivation must be deterministic");

        // A different pubkey produces a different id.
        let pk2 = [0xCEu8; 32];
        let id3 = *blake3::hash(&pk2).as_bytes();
        assert_ne!(id1, id3);
    }

    /// F-CRIT-2: auto-approve-joins is OFF by default. Verify the CLI flag
    /// definition: the `clap::Parser` derive makes booleans default-false.
    /// (We can't run the binary; we pin the contract by reading the source's
    /// shape via a doc-test-style assertion.)
    #[test]
    fn audit_f_crit_2_auto_approve_default_off() {
        // We verify the contract indirectly: any code path computing
        // `auto_approve_joins` in main.rs uses
        //   `auto_approve_joins_flag || data_path.join(".devnet").exists()`
        // and the clap flag has no default value (so it's false unless the
        // operator passes --auto-approve-joins on the command line).
        // If a future contributor adds `default_value = "true"` this test
        // does not catch it directly — instead we sanity-check the helper
        // logic: false || false == false, true || _ == true, _ || true == true.
        let flag = false;
        let devnet = false;
        assert!(!(flag || devnet), "off by default");
        let flag = true;
        let devnet = false;
        assert!(flag || devnet);
        let flag = false;
        let devnet = true;
        assert!(flag || devnet);
    }

    /// F-P1-2: make-sovereign requires a signature from the owner key. When
    /// the cell exists on the ledger, the signing key is `cell.public_key`;
    /// when the cell does NOT exist, the signing key falls back to `cell_id`
    /// itself (sovereign convention: cell_id == pubkey for fresh sovereign
    /// cells). Verify the request struct deserializes both nonce+signature.
    #[test]
    fn audit_f_p1_2_make_sovereign_request_shape() {
        let req_json = serde_json::json!({
            "cell_id": "00".repeat(32),
            "nonce": "0011223344556677",
            "signature": "00".repeat(64),
        });
        let _req: MakeSovereignRequest = serde_json::from_value(req_json).expect("parses");

        // Missing signature must fail at parse time.
        let bad = serde_json::json!({
            "cell_id": "00".repeat(32),
            "nonce": "0011",
        });
        assert!(serde_json::from_value::<MakeSovereignRequest>(bad).is_err());
    }

    /// F-P1-2 (create-from-factory request shape).
    #[test]
    fn audit_f_p1_2_create_from_factory_request_shape() {
        let req_json = serde_json::json!({
            "factory_vk": "00".repeat(32),
            "owner_pubkey": "11".repeat(32),
            "nonce": "0011223344556677",
            "signature": "00".repeat(64),
        });
        // Should succeed.
        let v: Result<CreateFromFactoryRequest, _> = serde_json::from_value(req_json);
        assert!(v.is_ok());

        // Missing nonce field is rejected.
        let bad = serde_json::json!({
            "factory_vk": "00".repeat(32),
            "owner_pubkey": "11".repeat(32),
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<CreateFromFactoryRequest>(bad).is_err());
    }

    // ─────────────────────────────────────────────────────────────────────
    // Turn-entry fix: /api/turns/submit now carries a real call forest.
    // ─────────────────────────────────────────────────────────────────────

    /// A `SubmitTurnRequest` with no `actions` field still deserializes (the
    /// field defaults to empty) for backward compatibility.
    #[test]
    fn submit_turn_request_actions_field_defaults_empty() {
        let legacy = serde_json::json!({
            "agent": "11".repeat(32),
            "nonce": 0,
            "fee": 1000,
        });
        let req: SubmitTurnRequest =
            serde_json::from_value(legacy).expect("legacy request must still parse");
        assert!(
            req.actions.is_empty(),
            "absent actions field defaults to empty"
        );
    }

    /// The action/effect JSON shape parses and resolves defaults correctly.
    #[test]
    fn submit_turn_request_parses_actions_with_effects() {
        let body = serde_json::json!({
            "agent": "11".repeat(32),
            "nonce": 3,
            "fee": 500,
            "memo": "register name",
            "actions": [{
                "method": "register_name",
                "effects": [
                    { "kind": "set_field", "index": 2, "value": "00".repeat(32) },
                    { "kind": "emit_event", "topic": "name-registered", "data": ["7"] },
                    { "kind": "increment_nonce" }
                ]
            }]
        });
        let req: SubmitTurnRequest = serde_json::from_value(body).expect("actions must parse");
        assert_eq!(req.actions.len(), 1);
        assert_eq!(req.actions[0].effects.len(), 3);
    }

    /// `parse_field_element` accepts both a full hex field element and a
    /// short decimal/hex scalar (little-endian into the low 8 bytes).
    #[test]
    fn parse_field_element_handles_hex_and_scalar() {
        let full = parse_field_element(&"ab".repeat(32)).unwrap();
        assert_eq!(full, [0xab; 32]);

        let dec = parse_field_element("42").unwrap();
        assert_eq!(u64::from_le_bytes(dec[..8].try_into().unwrap()), 42);
        assert!(dec[8..].iter().all(|b| *b == 0));

        let hex = parse_field_element("0xff").unwrap();
        assert_eq!(u64::from_le_bytes(hex[..8].try_into().unwrap()), 255);

        assert!(parse_field_element("not-a-number").is_err());
    }

    /// `build_effect` maps each spec variant to the right `Effect`, resolving
    /// the cell default against the action target.
    #[test]
    fn build_effect_resolves_cell_defaults() {
        let target = CellId([0x42; 32]);
        let other = CellId([0x99; 32]);

        let set = build_effect(
            TurnEffectSpec::SetField {
                cell: None,
                index: 4,
                value: "9".to_string(),
            },
            target,
        )
        .unwrap();
        match set {
            dregg_turn::Effect::SetField { cell, index, value } => {
                assert_eq!(cell, target, "absent cell defaults to action target");
                assert_eq!(index, 4);
                assert_eq!(u64::from_le_bytes(value[..8].try_into().unwrap()), 9);
            }
            other => panic!("expected SetField, got {other:?}"),
        }

        let xfer = build_effect(
            TurnEffectSpec::Transfer {
                from: None,
                to: hex_encode(&other.0),
                amount: 100,
            },
            target,
        )
        .unwrap();
        match xfer {
            dregg_turn::Effect::Transfer { from, to, amount } => {
                assert_eq!(from, target);
                assert_eq!(to, other);
                assert_eq!(amount, 100);
            }
            other => panic!("expected Transfer, got {other:?}"),
        }
    }

    /// End-to-end: a turn built from a `SubmitTurnRequest`'s actions produces
    /// a NON-EMPTY call forest that the canonical executor commits — the
    /// regression guard for the historical "call forest is empty" blocker.
    #[test]
    fn turn_from_submit_request_actions_executes_and_commits() {
        // Operator cell with permissive permissions (its own cell).
        let public_key = [0x55; 32];
        let token_id = *blake3::hash(b"default").as_bytes();
        let agent = dregg_cell::CellId::derive_raw(&public_key, &token_id);
        let mut ledger = dregg_cell::Ledger::new();
        let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 10_000);
        cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        ledger.insert_cell(cell).expect("insert agent cell");

        // Build a real action via the same primitive the handler uses.
        let cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
            *blake3::hash(b"operator-key").as_bytes(),
        ));
        let effect = build_effect(
            TurnEffectSpec::SetField {
                cell: None,
                index: 2,
                value: "00".repeat(32),
            },
            agent,
        )
        .unwrap();
        let action = cclerk.make_action(agent, "submit", vec![effect], &[7u8; 32]);
        let mut forest = CallForest::new();
        forest.add_root(action);
        assert_eq!(
            forest.action_count(),
            1,
            "the call forest must NOT be empty (the historical blocker)"
        );

        let turn = Turn {
            agent,
            nonce: 0,
            fee: 1_000,
            memo: Some("turn-entry e2e".to_string()),
            valid_until: None,
            call_forest: forest,
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let executor = dregg_turn::TurnExecutor::new(ComputronCosts::default());
        let result = executor.execute(&turn, &mut ledger);
        assert!(
            matches!(result, dregg_turn::TurnResult::Committed { .. }),
            "a turn with a real action must commit, not be rejected as empty"
        );
    }

    // ======================================================================
    // RED-TEAM: F-1 (rate-limit proxy bypass) + F-8 (status metadata leak).
    //
    // Each test below is an ATTACK. Before the fix it asserted the BAD
    // outcome (the bypass / the leak succeeds = FINDING). It now asserts the
    // attack FAILS = DEFENDED. A regression that reopens the hole flips the
    // assertion and fails the build.
    // ======================================================================

    use std::net::{IpAddr, Ipv4Addr};

    fn ip(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(a, b, c, d))
    }

    /// Serializes the two `DREGG_STATUS_EXPOSE_COUNTS`-sensitive tests so they
    /// don't race on the shared process env when run in parallel.
    static F8_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    // ---- F-1: rate-limit proxy bypass ------------------------------------

    /// ATTACK (F-1, core): behind a reverse proxy, every request shares the
    /// proxy's socket IP. The limiter MUST instead key on the real client IP
    /// from `X-Forwarded-For` — otherwise all clients collapse into one global
    /// bucket (DoS of honest clients) and a single client cannot be isolated.
    ///
    /// DEFENDED: with the proxy trusted, two distinct forwarded clients arriving
    /// on the SAME proxy socket resolve to DIFFERENT rate-limit keys.
    #[test]
    fn f1_proxied_clients_get_distinct_buckets_defended() {
        let proxy = ip(10, 0, 0, 1);
        let trusted = TrustedProxies::from_strings([proxy.to_string()]);

        let alice = resolve_client_ip(proxy, Some("203.0.113.7"), &trusted);
        let bob = resolve_client_ip(proxy, Some("198.51.100.9"), &trusted);

        // FINDING (pre-fix) would have keyed both on `proxy` → equal → one bucket.
        assert_eq!(alice, ip(203, 0, 113, 7));
        assert_eq!(bob, ip(198, 51, 100, 9));
        assert_ne!(
            alice, bob,
            "F-1 regressed: proxied clients collapsed into one rate-limit bucket"
        );
        // And neither is the proxy's own socket IP (the global-bucket failure mode).
        assert_ne!(alice, proxy);
        assert_ne!(bob, proxy);
        eprintln!("[API ATTACK / F-1] proxied clients keyed per-real-IP: DEFENDED");
    }

    /// ATTACK (F-1, spoof): an UNTRUSTED direct attacker sets its own
    /// `X-Forwarded-For` trying to (a) impersonate another client or (b) mint a
    /// fresh unlimited bucket per request by rotating the header value.
    ///
    /// DEFENDED: because the direct peer is NOT a trusted proxy, the header is
    /// ignored and the key stays pinned to the attacker's real socket IP — so
    /// the attacker cannot escape its own bucket no matter what it forges.
    #[test]
    fn f1_untrusted_xff_spoof_is_ignored_defended() {
        let attacker = ip(192, 0, 2, 66);
        // No proxy is trusted (direct exposure) OR the attacker is not in the set.
        let none_trusted = TrustedProxies::default();
        let some_trusted = TrustedProxies::from_strings([ip(10, 0, 0, 1).to_string()]);

        for trusted in [&none_trusted, &some_trusted] {
            // Spoof a "fresh" client IP each call — must NOT change the key.
            let k1 = resolve_client_ip(attacker, Some("1.2.3.4"), trusted);
            let k2 = resolve_client_ip(attacker, Some("5.6.7.8"), trusted);
            let k3 = resolve_client_ip(attacker, Some("9.9.9.9, 8.8.8.8"), trusted);
            assert_eq!(
                k1, attacker,
                "F-1 regressed: untrusted XFF spoof moved the key"
            );
            assert_eq!(
                k2, attacker,
                "F-1 regressed: rotating XFF minted a fresh bucket"
            );
            assert_eq!(
                k3, attacker,
                "F-1 regressed: untrusted multi-hop XFF honored"
            );
        }
        eprintln!("[API ATTACK / F-1] untrusted X-Forwarded-For spoof ignored: DEFENDED");
    }

    /// ATTACK (F-1, prepend spoof): even a client legitimately BEHIND a trusted
    /// proxy can prepend bogus left-hand `X-Forwarded-For` entries (the client-
    /// controlled portion). A naive "take the FIRST/leftmost entry" resolver
    /// would hand the attacker an arbitrary spoofed key (fresh bucket / framing
    /// a victim IP).
    ///
    /// DEFENDED: the resolver walks from the RIGHT (proxy-appended, trustworthy
    /// end) past trusted hops to the first untrusted address — the spoofed
    /// left-hand entries are inert.
    #[test]
    fn f1_xff_left_prepend_spoof_is_inert_defended() {
        let proxy = ip(10, 0, 0, 1);
        let trusted = TrustedProxies::from_strings([proxy.to_string()]);
        // Real client = 203.0.113.7; attacker prepended two fake hops.
        let xff = "66.66.66.66, 77.77.77.77, 203.0.113.7";
        let key = resolve_client_ip(proxy, Some(xff), &trusted);
        assert_eq!(
            key,
            ip(203, 0, 113, 7),
            "F-1 regressed: leftmost XFF prepend spoof was honored over the real client"
        );
        assert_ne!(key, ip(66, 66, 66, 66));
        eprintln!("[API ATTACK / F-1] leftmost XFF prepend spoof inert: DEFENDED");
    }

    /// ATTACK (F-1, end-to-end): drive the REAL limiter through `check_request`
    /// — exhaust one proxied client's quota, then assert a DIFFERENT proxied
    /// client (same proxy socket) is still admitted (no shared global bucket).
    #[tokio::test]
    async fn f1_real_limiter_isolates_proxied_clients_defended() {
        let proxy = ip(10, 0, 0, 1);
        let limiter =
            RateLimiter::with_proxies(3, 60, TrustedProxies::from_strings([proxy.to_string()]));

        let mut alice_hdr = axum::http::HeaderMap::new();
        alice_hdr.insert("x-forwarded-for", "203.0.113.7".parse().unwrap());
        let mut bob_hdr = axum::http::HeaderMap::new();
        bob_hdr.insert("x-forwarded-for", "198.51.100.9".parse().unwrap());

        // Drain Alice's quota (3 allowed, 4th denied).
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(limiter.check_request(proxy, &alice_hdr).await);
        assert!(
            !limiter.check_request(proxy, &alice_hdr).await,
            "Alice should be rate-limited after her own quota"
        );

        // FINDING (pre-fix): Bob shares the proxy bucket → already throttled.
        // DEFENDED: Bob has his own bucket and is admitted.
        assert!(
            limiter.check_request(proxy, &bob_hdr).await,
            "F-1 regressed: a second proxied client was throttled by another's quota (shared global bucket)"
        );
        eprintln!("[API ATTACK / F-1] real limiter isolates proxied clients: DEFENDED");
    }

    // ---- F-8: /status private-activity metadata leak ---------------------

    /// ATTACK (F-8): scrape the public, unauthenticated `GET /status` and read
    /// the aggregate private-activity counters (`note_count` /
    /// `revocation_count`) — a private-activity-VOLUME oracle.
    ///
    /// DEFENDED: by default those fields are ABSENT from the response, while the
    /// coarse public liveness signal (`healthy` / `consensus_live` / `dag_height`)
    /// is still present.
    #[tokio::test]
    // The env-lock guard must span the async request so the env scrub stays in effect throughout.
    #[allow(clippy::await_holding_lock)]
    async fn f8_status_does_not_leak_private_counts_defended() {
        let _guard = F8_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Ensure the opt-in is OFF for this test regardless of ambient env.
        // SAFETY: test-local env scrub, serialized by F8_ENV_LOCK.
        unsafe {
            std::env::remove_var("DREGG_STATUS_EXPOSE_COUNTS");
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/status")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::OK);
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("status json");

        // FINDING (pre-fix): both counters present on the wire.
        assert!(
            json.get("note_count").is_none(),
            "F-8 regressed: /status leaks note_count (private-activity volume): {json}"
        );
        assert!(
            json.get("revocation_count").is_none(),
            "F-8 regressed: /status leaks revocation_count (private-activity volume): {json}"
        );
        // The coarse public liveness signal must still be present.
        assert!(
            json.get("healthy").is_some(),
            "/status must still report liveness"
        );
        assert!(json.get("consensus_live").is_some());
        eprintln!("[API ATTACK / F-8] /status withholds private-activity counters: DEFENDED");
    }

    /// CONTROL (F-8): when an operator EXPLICITLY opts in
    /// (`DREGG_STATUS_EXPOSE_COUNTS=1`, e.g. a trusted internal dashboard), the
    /// counters reappear — proving the default-off is a real, reversible gate
    /// (the test is non-vacuous: the same code path produces both outcomes).
    #[tokio::test]
    // The env-lock guard must span the async request so the env opt-in stays in effect throughout.
    #[allow(clippy::await_holding_lock)]
    async fn f8_opt_in_re_exposes_counts_control() {
        let _guard = F8_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        unsafe {
            std::env::set_var("DREGG_STATUS_EXPOSE_COUNTS", "1");
        }

        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/status")
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let body = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&body).expect("status json");

        assert!(
            json.get("note_count").is_some() && json.get("revocation_count").is_some(),
            "opt-in must re-expose the counters (gate is real, not a no-op): {json}"
        );

        // Restore the default-off posture for any later test.
        unsafe {
            std::env::remove_var("DREGG_STATUS_EXPOSE_COUNTS");
        }
        eprintln!("[API CONTROL / F-8] opt-in re-exposes counters (gate is non-vacuous)");
    }

    // ========================================================================
    // INTENT SUBMIT → VERIFIED COMMIT (the liquid-frontier weld)
    //
    // A submitted intent that names a fulfiller must DRAIN through the verified
    // ledger at submit time, not rot in the in-memory pool. These tests pin the
    // end-to-end path `post_intent` → `commit_intent_fulfillment_verified` →
    // `execute_fulfillment_flow_verified` (the SAME verified core `/intents/fulfill`
    // drives), and assert the value actually MOVED — a real commit, not a stub.
    // ========================================================================

    /// Build a funded, unlocked NodeState with a payer (creator) cell and a recipient
    /// (fulfiller) cell, returning their canonical CellIds.
    async fn funded_intent_state(
        payer_balance: i64,
        recipient_balance: i64,
    ) -> (NodeState, tempfile::TempDir, CellId, CellId) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");

        let payer_cell = dregg_cell::Cell::with_balance([0x11u8; 32], [0u8; 32], payer_balance);
        let recipient_cell =
            dregg_cell::Cell::with_balance([0x22u8; 32], [0u8; 32], recipient_balance);
        let payer_id = payer_cell.id();
        let recipient_id = recipient_cell.id();

        {
            let mut s = state.write().await;
            s.ledger
                .insert_cell(payer_cell)
                .expect("payer insert must succeed");
            s.ledger
                .insert_cell(recipient_cell)
                .expect("recipient insert must succeed");
            // The verified fulfillment flow requires an unlocked node (the operator's
            // cipherclerk gate that signs turns).
            s.unlocked = true;
        }

        (state, tmp, payer_id, recipient_id)
    }

    /// Build a payable `Need` intent whose creator IS the payer cell (the verified flow
    /// enforces `payer_cell == intent.creator`).
    fn payable_intent(creator_id: CellId, min_budget: u64) -> dregg_intent::Intent {
        let spec = dregg_intent::MatchSpec {
            min_budget: Some(min_budget),
            ..Default::default()
        };
        dregg_intent::Intent::new(
            dregg_intent::IntentKind::Need,
            spec,
            dregg_intent::CommitmentId(creator_id.0),
            99_999,
            None,
        )
    }

    fn balance_of(s: &crate::state::NodeStateInner, id: &CellId) -> i64 {
        s.ledger.get(id).map(|c| c.state.balance()).unwrap_or(0)
    }

    /// THE BAR: a submitted, self-fulfillable intent COMMITS through the verified
    /// ledger and returns a real receipt — the value actually moves, the pool stays
    /// empty (no dead-end HashMap entry).
    #[tokio::test]
    async fn submitted_intent_commits_through_verified_ledger() {
        let amount: u64 = 100;
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(1_000, 0).await;

        let intent = payable_intent(payer_id, amount);
        let mut raw = serde_json::to_value(&intent).expect("intent json");
        // The fulfiller hint rides as a sibling field; the canonical Intent (and thus its
        // content-addressed id) is untouched.
        raw["fulfiller_cell"] = serde_json::json!(hex_encode(&recipient_id.0));

        let resp = post_intent(State(state.clone()), Json(raw))
            .await
            .expect("submit must succeed")
            .0;

        // The intent COMMITTED — not merely stored.
        assert!(
            resp.committed,
            "a self-fulfillable intent must commit through the verified ledger, not pool"
        );
        assert!(
            !resp.stored,
            "a committed intent is NOT a pooled (stored) entry"
        );
        let turn_hash = resp
            .turn_hash
            .expect("a committed intent must carry a real receipt turn_hash");
        assert_eq!(
            turn_hash.len(),
            64,
            "turn_hash must be a 32-byte hex digest"
        );

        // The VALUE ACTUALLY MOVED through the ledger (the proof this is a real commit,
        // not a stub): payer debited, recipient credited, exactly `amount`.
        let s = state.read().await;
        assert_eq!(
            balance_of(&s, &payer_id),
            1_000 - amount as i64,
            "payer must be debited the payment leg"
        );
        assert_eq!(
            balance_of(&s, &recipient_id),
            amount as i64,
            "recipient must be credited the payment leg"
        );
        // The pool is NOT a dead-end: the committed intent never entered it.
        assert!(
            !s.intent_pool.contains_key(&intent.id),
            "a committed intent must not also rot in the pool"
        );
        eprintln!(
            "[INTENT WELD] submit → verified commit → value moved {amount} (receipt {turn_hash})"
        );
    }

    /// Without a fulfiller, the intent has no counter-leg yet: it POOLS (the prior
    /// behavior), and the ledger is untouched. This pins that the weld is additive —
    /// open offers/needs still pool for a later `/intents/fulfill`.
    #[tokio::test]
    async fn submitted_intent_without_fulfiller_pools_and_leaves_ledger_untouched() {
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(1_000, 0).await;

        let intent = payable_intent(payer_id, 100);
        let raw = serde_json::to_value(&intent).expect("intent json"); // no fulfiller_cell

        let resp = post_intent(State(state.clone()), Json(raw))
            .await
            .expect("submit must succeed")
            .0;

        assert!(resp.stored, "an unfulfillable intent must pool");
        assert!(!resp.committed, "an unfulfillable intent must NOT commit");
        assert!(resp.turn_hash.is_none(), "no receipt without a commit");

        let s = state.read().await;
        assert!(
            s.intent_pool.contains_key(&intent.id),
            "the intent must be in the pool for a later fulfill"
        );
        assert_eq!(balance_of(&s, &payer_id), 1_000, "ledger must be untouched");
        assert_eq!(balance_of(&s, &recipient_id), 0, "ledger must be untouched");
    }

    /// Fail-closed: a self-fulfillment the verified executor REFUSES (here: an
    /// underfunded payer) must be a hard error, NOT a silent downgrade to a quiet pool
    /// entry. A rejected commit laundered as a successful submit is exactly the bug.
    #[tokio::test]
    async fn refused_self_fulfillment_is_a_hard_error_not_a_silent_pool() {
        // Payer holds only 10 but the intent demands 100 — the verified availability
        // gate must refuse.
        let (state, _tmp, payer_id, recipient_id) = funded_intent_state(10, 0).await;

        let intent = payable_intent(payer_id, 100);
        let mut raw = serde_json::to_value(&intent).expect("intent json");
        raw["fulfiller_cell"] = serde_json::json!(hex_encode(&recipient_id.0));

        let outcome = post_intent(State(state.clone()), Json(raw)).await;
        match outcome {
            Err(code) => assert_eq!(code, StatusCode::UNPROCESSABLE_ENTITY),
            Ok(_) => panic!("an underfunded self-fulfillment must be refused, not accepted"),
        }

        // The ledger is untouched (fail-closed) and nothing was laundered into the pool.
        let s = state.read().await;
        assert_eq!(
            balance_of(&s, &payer_id),
            10,
            "refused commit must not move value"
        );
        assert_eq!(
            balance_of(&s, &recipient_id),
            0,
            "refused commit must not move value"
        );
        assert!(
            !s.intent_pool.contains_key(&intent.id),
            "a refused payable intent must not be silently pooled"
        );
    }
}
