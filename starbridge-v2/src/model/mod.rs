//! Data models — the node's wire contract, mirrored.
//!
//! These structs are deliberate copies of the node's JSON response types
//! (`node/src/api.rs`, `node/src/events.rs`). The native shell is a CLIENT: it
//! speaks HTTP+SSE to a dregg node and never links the executor or the Lean
//! archive. Mirroring the wire types (rather than linking `dregg-sdk`, which
//! pulls `libdregg_lean.a` on native) keeps this crate light and its
//! dependency on the node a *protocol* dependency, not a *code* dependency.
//!
//! INVARIANT to maintain: when `node/src/api.rs` changes a response shape, the
//! mirror here must follow. A future build-out lane (docs/STARBRIDGE-V2.md
//! §"Build-out lanes") can replace these hand-mirrors with a shared
//! `dregg-wire-types` crate so the contract is single-sourced.

use serde::{Deserialize, Serialize};

/// `GET /status` — node liveness + the SWAP producer surface.
/// Mirrors `api::StatusResponse`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NodeStatus {
    pub healthy: bool,
    pub peer_count: usize,
    pub latest_height: u64,
    pub dag_height: u64,
    pub block_count: usize,
    pub consensus_live: bool,
    pub federation_mode: String,
    pub public_key: String,
    /// `"lean"` or `"rust"` — the authoritative state producer on the commit
    /// path. The shell surfaces this honestly: a node running the legacy Rust
    /// producer is visibly NOT running the verified semantics.
    pub state_producer: String,
    pub lean_producer: bool,
    pub full_turn_proving: bool,
    pub producer_covered_effects: usize,
}

/// `GET /api/cells` entry. Mirrors `api::CellListEntry`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct CellListEntry {
    pub id: String,
    /// THE EPOCH: signed (issuer wells carry −supply).
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub has_program: bool,
    pub found: bool,
}

/// `GET /api/cell/{id}` — the inspector's per-cell detail.
/// Mirrors the load-bearing fields of `api::CellDetailResponse` (the
/// `program` field, a rich `CellProgramView`, is rendered from its JSON form
/// rather than mirrored as a typed struct in the scaffold).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct CellDetail {
    pub id: String,
    pub found: bool,
    pub balance: i64,
    pub nonce: u64,
    pub capability_count: usize,
    pub has_delegate: bool,
    pub delegate: Option<String>,
    pub has_program: bool,
    pub public_key: String,
    pub token_id: String,
    pub proved_state: bool,
    pub delegation_epoch: u64,
    pub state_commitment: String,
    pub program_kind: String,
    /// Raw `[FieldElement; 16]` slots, hex-encoded (64 chars each).
    #[serde(default)]
    pub fields: Vec<String>,
    /// The self-describing program view, kept as raw JSON in the scaffold.
    #[serde(default)]
    pub program: Option<serde_json::Value>,
}

/// `GET /api/receipts` entry. Mirrors `api::ReceiptInfo`.
#[derive(Debug, Clone, Deserialize, Serialize)]
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

/// One committed receipt off the SSE stream `GET /api/events/stream`.
/// Mirrors the summary fields of `events::ReceiptEvent` (the embedded full
/// canonical `TurnReceipt` is left as raw JSON — the shell renders summaries
/// and drills into the raw form in the inspector).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ReceiptEvent {
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    #[serde(default)]
    pub cells: Vec<String>,
    #[serde(default)]
    pub kinds: Vec<String>,
    pub height: u64,
    pub has_proof: bool,
    pub finality: String,
    pub timestamp: i64,
}

/// One **Dregg Computer** (a vat) off the DreggNet gateway's designed
/// `GET /v1/vats` roster — THE NAMED SEAM to the rental trunk
/// (DREGG-COMPUTER.md build order #3: the `POST /v1/vats` + `GET /v1/vats/{id}`
/// handlers over `ServerFleet`, behind the funded-lease gate).
///
/// A vat is a persistent server whose identity is a content-addressed CELL
/// (`ServerRecord.cell_id`, DreggNet control/src/server.rs) — so this mirror
/// carries the cell id as the primary key, the reachable `endpoint`
/// (`ServerRecord.endpoint` is build-order #1 and may be absent while the vat
/// is asleep or the overlay route unbuilt — hence `Option`), the funded-lease
/// truth (`funded` reads the REAL reserve admission, never a self-asserted
/// flag), the per-period settle count, the committed `checkpoint_root` a
/// sleeping vat wakes from, and the witness discipline (`"full"` proof-as-you-go
/// / `"symbolic"` defer-verify-later — `WitnessMode`, turn/src/collapse.rs).
///
/// Every field except `cell_id` is `#[serde(default)]`-tolerant: the gateway
/// contract is still landing on the DreggNet side, and a missing field must
/// degrade to an honest empty rather than a parse failure (the same tolerance
/// discipline `BlockInfo` holds).
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct VatEntry {
    /// The vat's identity — the content-addressed cell id (hex), derived from
    /// `(owner, app, name)`. This is also the capability scope: the credential
    /// that reaches this computer carries exactly `vat:<cell_id>`.
    pub cell_id: String,
    /// The human name its owner gave it (`"mybox"`).
    #[serde(default)]
    pub name: String,
    /// The owning account subject (the funded-lease principal).
    #[serde(default)]
    pub owner: String,
    /// The reachable endpoint URL (loopback in dev; overlay-routed later).
    /// `None` = not reachable yet (asleep, or the data plane unbuilt).
    #[serde(default)]
    pub endpoint: Option<String>,
    /// Lifecycle as a free string (`"running"` / `"sleeping"` / `"created"` …) —
    /// tolerant so a new provider state never breaks the parse.
    #[serde(default)]
    pub state: String,
    /// The funded-lease admission truth — read from the owner's REAL on-chain
    /// reserve at authorize time, never self-asserted.
    #[serde(default)]
    pub funded: bool,
    /// Uptime periods settled so far (the exactly-once per-period settle).
    #[serde(default)]
    pub paid_periods: u64,
    /// The committed state root a sleeping vat checkpointed to (hex), if any —
    /// the cell-ness of the computer: sleep = commit, wake = restore.
    #[serde(default)]
    pub checkpoint_root: Option<String>,
    /// The witness discipline: `"full"` (every turn's Merkle witness
    /// materialized, receipt immediately publishable) or `"symbolic"` (state
    /// fully applies, witness deferred until a collapse re-derives it
    /// fail-closed). Empty = unknown (an old gateway) — treat as full.
    #[serde(default)]
    pub witness_mode: String,
}

/// `GET /api/federations` entry. Mirrors `api::FederationInfo`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct FederationInfo {
    pub id: String,
    pub federation_id: String,
    pub committee_epoch: u64,
    pub threshold: u32,
    pub member_count: usize,
    #[serde(default)]
    pub members: Vec<String>,
    pub is_local: bool,
    pub latest_height: u64,
    pub latest_root: Option<String>,
    pub num_finalized_roots: usize,
}

/// A block in the blocklace DAG. Mirrors the relevant subset of
/// `GET /api/blocklace/blocks`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct BlockInfo {
    #[serde(default)]
    pub height: u64,
    #[serde(default)]
    pub hash: String,
    #[serde(default)]
    pub creator: String,
    #[serde(default)]
    pub seq: u64,
}

// ===========================================================================
// TURN COMPOSITION — the `POST /turn/submit` request shape.
//
// Mirrors `api::SubmitTurnRequest` / `TurnActionSpec` / `TurnEffectSpec`.
// The TurnComposer view builds these; submission is a build-out lane (it
// needs local key custody to sign, OR routes through the node's operator
// cipherclerk for the thin-client effects below).
// ===========================================================================

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SubmitTurnRequest {
    pub agent: String,
    pub nonce: u64,
    pub fee: u64,
    pub memo: Option<String>,
    #[serde(default)]
    pub actions: Vec<TurnActionSpec>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TurnActionSpec {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    pub effects: Vec<TurnEffectSpec>,
}

/// The JSON-friendly projection of the on-chain `Effect` enum that a thin
/// HTTP client can drive. Mirrors `api::TurnEffectSpec`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TurnEffectSpec {
    SetField {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
        index: usize,
        value: String,
    },
    Transfer {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        from: Option<String>,
        to: String,
        amount: u64,
    },
    EmitEvent {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
        topic: String,
        #[serde(default)]
        data: Vec<String>,
    },
    IncrementNonce {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cell: Option<String>,
    },
}

impl TurnEffectSpec {
    /// Short human label for the composer's effect list.
    pub fn label(&self) -> String {
        match self {
            TurnEffectSpec::SetField { index, .. } => format!("set_field[{index}]"),
            TurnEffectSpec::Transfer { to, amount, .. } => {
                format!("transfer {amount} → {}", short_id(to))
            }
            TurnEffectSpec::EmitEvent { topic, .. } => format!("emit {topic}"),
            TurnEffectSpec::IncrementNonce { .. } => "increment_nonce".to_string(),
        }
    }
}

/// Trim a 64-char hex id to `abcd…wxyz` for display.
pub fn short_id(id: &str) -> String {
    if id.len() <= 12 {
        id.to_string()
    } else {
        format!("{}…{}", &id[..6], &id[id.len() - 4..])
    }
}

/// `POST /cipherclerk/unlock` response. Mirrors `api::UnlockResponse`.
///
/// Unlocking the node's operator cipherclerk is what lets the cockpit submit
/// turns it will commit: the node signs every operator turn as its own cell
/// (confused-deputy hardening), so "local key custody" on the cockpit side is
/// the operator passphrase + the returned bearer token, which `require_auth`
/// then checks on every write route (incl. `/turn/submit`).
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct UnlockResponse {
    pub success: bool,
    /// The API bearer token the cockpit attaches as `Authorization: Bearer …`
    /// on every subsequent write (the node derives it from the passphrase seed).
    #[serde(default)]
    pub bearer_token: Option<String>,
    #[serde(default)]
    pub error: Option<String>,
}

/// `POST /turn/submit` response. Mirrors `api::SubmitTurnResponse`.
///
/// `accepted` is the truth of whether the node's verified executor COMMITTED the
/// turn to its ledger (the same `gateOK`/conservation/authority path the node
/// uses for every turn). A refusal carries the reason in `error` / `turn_hash`
/// (the handler reports refusals in-band with a 200 body), so the cockpit can
/// surface an honest "the node refused this save: …" instead of a silent drop.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    #[serde(default)]
    pub turn_hash: Option<String>,
    #[serde(default)]
    pub proof_status: Option<String>,
    #[serde(default)]
    pub has_witness: bool,
    #[serde(default)]
    pub witness_count: usize,
    #[serde(default)]
    pub error: Option<String>,
}

/// `POST /turns/submit` response. Mirrors `api::SubmitSignedTurnResponse`.
///
/// This is the CLIENT-SIGNED ingest path: the cockpit posts a postcard-encoded
/// `dregg_sdk::SignedTurn` (signed under its OWN ed25519 key — the node never
/// holds it, unlike the operator `/turn/submit` path) and the node verifies the
/// signature, runs the turn through the same `gateOK`/conservation/authority
/// gates, and commits it under the CLIENT'S authority. `accepted` is the truth of
/// whether the node committed it; `signer` echoes the recovered signer cell so the
/// cockpit can confirm whose authority bound the turn. A refusal carries the reason
/// in `error` (the handler reports refusals in-band with a 200 body), so the cockpit
/// surfaces an honest "the node refused this turn: …" instead of a silent drop.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct SubmitSignedTurnResponse {
    pub accepted: bool,
    #[serde(default)]
    pub turn_hash: Option<String>,
    /// The recovered signer cell (hex), echoed back so the cockpit can confirm
    /// whose authority the node bound the turn to.
    #[serde(default)]
    pub signer: Option<String>,
    #[serde(default)]
    pub action_count: usize,
    /// The proof lane verdict as a snake_case string (e.g. `"proof_pending"`,
    /// `"not_required"`, `"not_committed"`) — kept as a free `String` so a new
    /// variant on the node doesn't break the parse.
    #[serde(default)]
    pub proof_status: Option<String>,
    #[serde(default)]
    pub has_witness: bool,
    #[serde(default)]
    pub witness_count: usize,
    #[serde(default)]
    pub error: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `/v1/vats` mirror is TOLERANT: a minimal gateway row (just the cell
    /// id) parses with honest defaults, and a full row round-trips every field.
    /// This is the wire-contract tooth for the Dregg Computer roster — the
    /// gateway is still landing on the DreggNet side, so the mirror must never
    /// turn a missing optional field into a parse failure.
    #[test]
    fn vat_entry_parses_tolerantly_and_roundtrips() {
        // Minimal: only the identity — everything else defaults.
        let minimal: VatEntry =
            serde_json::from_str(&format!(r#"{{"cell_id":"{}"}}"#, "dc".repeat(32))).unwrap();
        assert_eq!(minimal.cell_id, "dc".repeat(32));
        assert!(minimal.endpoint.is_none());
        assert!(!minimal.funded);
        assert_eq!(minimal.paid_periods, 0);
        assert!(minimal.witness_mode.is_empty()); // unknown → caller treats as full

        // Full: the shape the designed gateway returns for a running vat.
        let full = VatEntry {
            cell_id: "dc".repeat(32),
            name: "mybox".into(),
            owner: "acct:renter".into(),
            endpoint: Some("http://127.0.0.1:8730".into()),
            state: "running".into(),
            funded: true,
            paid_periods: 3,
            checkpoint_root: None,
            witness_mode: "full".into(),
        };
        let json = serde_json::to_string(&full).unwrap();
        let back: VatEntry = serde_json::from_str(&json).unwrap();
        assert_eq!(back, full);

        // An unknown extra field from a newer gateway is ignored, not fatal.
        let ahead: VatEntry = serde_json::from_str(&format!(
            r#"{{"cell_id":"{}","state":"sleeping","checkpoint_root":"{}","novel_field":7}}"#,
            "5e".repeat(32),
            "9a".repeat(32)
        ))
        .unwrap();
        assert_eq!(ahead.state, "sleeping");
        assert_eq!(
            ahead.checkpoint_root.as_deref(),
            Some("9a".repeat(32).as_str())
        );
    }
}
