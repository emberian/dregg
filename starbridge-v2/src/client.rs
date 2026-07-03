//! The node connection — an HTTP+SSE client against a dregg node.
//!
//! The shell speaks the node's wire contract (`node/src/api.rs` routes,
//! `node/src/events.rs` SSE stream). In the scaffold this layer ships two
//! implementations behind one interface:
//!
//!   * [`NodeClient::mock`] — an in-process fixture so the gpui shell renders
//!     real components with real data shapes WITHOUT a running node. This is
//!     the default the scaffold boots into.
//!   * [`NodeClient::http`] — points at a real node base URL. The fetch
//!     methods are wired to the routes; the SSE receipt stream is a build-out
//!     lane (it needs to be driven on gpui's async executor — see
//!     docs/STARBRIDGE-V2.md §"Build-out lanes").
//!
//! Both return the same [`crate::model`] types, so the views never know which
//! backend they are bound to.

use crate::model::{
    BlockInfo, CellListEntry, FederationInfo, NodeStatus, ReceiptEvent, SubmitSignedTurnResponse,
    SubmitTurnRequest, SubmitTurnResponse, TurnActionSpec, TurnEffectSpec, UnlockResponse,
    VatEntry,
};

/// THE NAMED SEAM to the DreggNet gateway's vat roster — the designed
/// `GET /v1/vats` route (DREGG-COMPUTER.md build order #3: gateway handlers
/// over `ServerFleet`, behind the funded-lease admission gate). The desktop's
/// "My Dregg Computers" surface reads [`NodeClient::vats`] against this path;
/// until the gateway lands on the DreggNet side, the `Mock` backend's
/// [`mock::vats`] fixture carries the same wire shape.
pub const VATS_ROUTE: &str = "/v1/vats";

/// Where the shell gets its data.
#[derive(Clone)]
pub enum NodeClient {
    /// In-process fixtures — the scaffold's default. No network.
    Mock,
    /// A real node at `base_url` (e.g. `http://127.0.0.1:8080`).
    ///
    /// `bearer` is the operator API token: empty until the cockpit unlocks the
    /// node ([`NodeClient::unlock`]), then attached as `Authorization: Bearer …`
    /// on every write route. The node's `require_auth` middleware gates
    /// `/turn/submit` (and the rest of the write surface) on it, so a turn-submit
    /// without it is a 401. This IS the cockpit's local key custody for node
    /// writes: the node signs every operator turn as its OWN cipherclerk
    /// (confused-deputy hardening), so the cockpit's "key" is the passphrase that
    /// unlocks that cipherclerk + the bearer it mints.
    Http {
        base_url: String,
        bearer: Option<String>,
    },
}

impl NodeClient {
    pub fn mock() -> Self {
        NodeClient::Mock
    }

    pub fn http(base_url: impl Into<String>) -> Self {
        NodeClient::Http {
            base_url: base_url.into(),
            bearer: None,
        }
    }

    /// An HTTP client already carrying an operator bearer token (e.g. one a prior
    /// [`NodeClient::unlock`] minted), so its write routes authenticate.
    pub fn http_authed(base_url: impl Into<String>, bearer: impl Into<String>) -> Self {
        NodeClient::Http {
            base_url: base_url.into(),
            bearer: Some(bearer.into()),
        }
    }

    /// The operator bearer token this client carries, if any (the unlocked-node
    /// write credential).
    pub fn bearer(&self) -> Option<&str> {
        match self {
            NodeClient::Http { bearer, .. } => bearer.as_deref(),
            NodeClient::Mock => None,
        }
    }

    pub fn describe(&self) -> String {
        match self {
            NodeClient::Mock => "mock (no node)".to_string(),
            NodeClient::Http { base_url, .. } => base_url.clone(),
        }
    }

    pub fn is_live(&self) -> bool {
        matches!(self, NodeClient::Http { .. })
    }

    // --- reads ------------------------------------------------------------

    pub fn status(&self) -> anyhow::Result<NodeStatus> {
        match self {
            NodeClient::Mock => Ok(mock::status()),
            NodeClient::Http { base_url, .. } => http_get(base_url, "/status"),
        }
    }

    pub fn cells(&self) -> anyhow::Result<Vec<CellListEntry>> {
        match self {
            NodeClient::Mock => Ok(mock::cells()),
            NodeClient::Http { base_url, .. } => http_get(base_url, "/api/cells"),
        }
    }

    pub fn receipts(&self) -> anyhow::Result<Vec<ReceiptEvent>> {
        match self {
            NodeClient::Mock => Ok(mock::receipts()),
            // The non-stream snapshot uses /api/starbridge/receipts; the
            // scaffold maps those summary fields onto ReceiptEvent.
            NodeClient::Http { base_url, .. } => http_get(base_url, "/api/receipts"),
        }
    }

    /// A TOLERANT count of the node's committed receipts (`GET /api/receipts`,
    /// parsed as a raw JSON array — that endpoint returns the FULL receipt shape
    /// (`agent`/`pre_state`/`post_state`/`action_count`/…), a superset of the
    /// SSE-summary [`ReceiptEvent`] [`Self::receipts`] decodes, so a typed parse
    /// rejects it). This is the empirical write-back probe: re-read it after a
    /// turn and see whether the node's ledger grew, without coupling to the exact
    /// receipt schema.
    pub fn receipts_count(&self) -> anyhow::Result<usize> {
        match self {
            NodeClient::Mock => Ok(mock::receipts().len()),
            NodeClient::Http { base_url, .. } => {
                let arr: Vec<serde_json::Value> = http_get(base_url, "/api/receipts")?;
                Ok(arr.len())
            }
        }
    }

    /// The RAW receipt array (`GET /api/receipts`) as untyped JSON values —
    /// newest first. Used to reflect the chain head without coupling to the exact
    /// receipt schema (the endpoint carries the full receipt shape, a superset of
    /// the SSE-summary [`ReceiptEvent`]).
    pub fn receipts_raw(&self) -> anyhow::Result<Vec<serde_json::Value>> {
        match self {
            NodeClient::Mock => Ok(Vec::new()),
            NodeClient::Http { base_url, .. } => http_get(base_url, "/api/receipts"),
        }
    }

    pub fn federations(&self) -> anyhow::Result<Vec<FederationInfo>> {
        match self {
            NodeClient::Mock => Ok(mock::federations()),
            NodeClient::Http { base_url, .. } => http_get(base_url, "/api/federations"),
        }
    }

    pub fn blocks(&self) -> anyhow::Result<Vec<BlockInfo>> {
        match self {
            NodeClient::Mock => Ok(mock::blocks()),
            NodeClient::Http { base_url, .. } => http_get(base_url, "/api/blocklace/blocks"),
        }
    }

    /// The vats this account can reach — **your Dregg Computers** — off the
    /// gateway's designed [`VATS_ROUTE`] (`GET /v1/vats`). Carries the client's
    /// bearer when it has one: the live gateway gates the roster on the account
    /// credential (a `dga1_…` token whose caps resolve the subject), so an
    /// unauthed read against a real gateway surfaces an honest 401 rather than
    /// someone else's fleet. The `Mock` backend returns the [`mock::vats`]
    /// fixture — the same wire shape, no network — which is the v0 stand-in
    /// until the DreggNet gateway route lands (the named seam).
    pub fn vats(&self) -> anyhow::Result<Vec<VatEntry>> {
        match self {
            NodeClient::Mock => Ok(mock::vats()),
            NodeClient::Http { base_url, bearer } => {
                http_get_authed(base_url, VATS_ROUTE, bearer.as_deref())
            }
        }
    }

    /// The SSE receipt-stream URL for this node (`/api/events/stream`). Resume is
    /// NOT a query param — the node resumes from the `Last-Event-ID` HEADER (see
    /// `node/src/events.rs`), which the reader sets on a reconnect. The `_resume`
    /// argument is kept for call-site clarity (the reader passes its cursor) but is
    /// not folded into the URL. `None` for the mock backend (it has no stream).
    pub fn events_stream_url(&self, _resume: Option<u64>) -> Option<String> {
        match self {
            NodeClient::Mock => None,
            NodeClient::Http { base_url, .. } => Some(format!("{base_url}/api/events/stream")),
        }
    }

    // --- writes -----------------------------------------------------------

    /// UNLOCK the node's operator cipherclerk with `passphrase` (`POST
    /// /cipherclerk/unlock`) and return the bearer token the node mints. This is
    /// the cockpit's local key custody for node writes: the node signs every
    /// operator turn as its OWN cipherclerk (confused-deputy hardening), so the
    /// cockpit's credential is the passphrase that unlocks that cipherclerk plus
    /// the bearer token `require_auth` then checks on `/turn/submit`. On a fresh
    /// node the first unlock SETS the passphrase; thereafter it must match.
    ///
    /// Returns an error if the node refuses (bad passphrase) or carries no token.
    pub fn unlock(&self, passphrase: &str) -> anyhow::Result<String> {
        match self {
            NodeClient::Mock => Ok("mock-bearer".to_string()),
            NodeClient::Http { base_url, .. } => {
                let body = serde_json::json!({ "passphrase": passphrase });
                let resp: UnlockResponse =
                    http_post_json(base_url, "/cipherclerk/unlock", None, &body)?;
                if !resp.success {
                    anyhow::bail!(
                        "node unlock refused: {}",
                        resp.error.unwrap_or_else(|| "unknown".into())
                    );
                }
                resp.bearer_token
                    .ok_or_else(|| anyhow::anyhow!("node unlock returned no bearer token"))
            }
        }
    }

    /// Return a copy of this client carrying `bearer` as its operator token, so
    /// its write routes authenticate. (`NodeClient` is by-value `Clone`; the
    /// cockpit holds the authed copy after an [`Self::unlock`].)
    pub fn with_bearer(&self, bearer: impl Into<String>) -> NodeClient {
        match self {
            NodeClient::Mock => NodeClient::Mock,
            NodeClient::Http { base_url, .. } => NodeClient::Http {
                base_url: base_url.clone(),
                bearer: Some(bearer.into()),
            },
        }
    }

    /// SUBMIT a turn to the node's verified executor (`POST /turn/submit`) and
    /// return the typed [`SubmitTurnResponse`]. This is the REAL ingest path: the
    /// node runs the turn through the same `gateOK`/conservation/authority gates
    /// it uses for every turn, commits it to its ledger (growing `/api/receipts`),
    /// signs it as the operator cipherclerk, and gossips/orders it. A refusal is
    /// reported IN-BAND (`accepted: false`, `error: …`) — no executor bypass.
    ///
    /// Requires the operator bearer token (`require_auth`): call [`Self::unlock`]
    /// first and bind it with [`Self::with_bearer`], or use [`Self::http_authed`].
    /// Without it the node returns 401 and this surfaces an honest error.
    pub fn submit_turn(&self, req: &SubmitTurnRequest) -> anyhow::Result<SubmitTurnResponse> {
        match self {
            NodeClient::Mock => Ok(SubmitTurnResponse {
                accepted: true,
                turn_hash: Some(format!("mock-receipt:{}-actions", req.actions.len())),
                proof_status: Some("not_required".into()),
                ..Default::default()
            }),
            NodeClient::Http { base_url, bearer } => {
                http_post_json(base_url, "/turn/submit", bearer.as_deref(), req)
            }
        }
    }

    /// SUBMIT a CLIENT-SIGNED turn to the node (`POST /turns/submit`, plural). The
    /// turn is a [`dregg_sdk::SignedTurn`] the cockpit signed under its OWN ed25519
    /// key (the node never holds it — distinct from the operator [`Self::submit_turn`]
    /// path, where the node signs as its own cipherclerk). The body is the
    /// postcard-encoded `SignedTurn` (`application/octet-stream`); the node verifies
    /// the signature, runs the turn through the same `gateOK`/conservation/authority
    /// gates, and commits it under the CLIENT'S authority. A refusal is reported
    /// IN-BAND ([`SubmitSignedTurnResponse::accepted`] `= false`, `error: …`).
    ///
    /// Requires the operator bearer token (`require_auth` gates this route too) AND
    /// the node be unlocked: call [`Self::unlock`] and bind it with
    /// [`Self::with_bearer`], or use [`Self::http_authed`]. The client cell should
    /// already EXIST (its first turn can't materialize it) — call
    /// [`Self::faucet_materialize`] once on a fresh key.
    #[cfg(feature = "embedded-executor")]
    pub fn submit_signed_turn(
        &self,
        signed: &dregg_sdk::SignedTurn,
    ) -> anyhow::Result<SubmitSignedTurnResponse> {
        match self {
            NodeClient::Mock => Ok(SubmitSignedTurnResponse {
                accepted: true,
                turn_hash: Some("mock-signed-receipt".into()),
                proof_status: Some("not_required".into()),
                ..Default::default()
            }),
            NodeClient::Http { base_url, bearer } => {
                let bytes = postcard::to_stdvec(signed)?;
                http_post_octet(base_url, "/turns/submit", bearer.as_deref(), bytes)
            }
        }
    }

    /// MATERIALIZE a recipient cell at balance 0 via the node's faucet
    /// (`POST /api/faucet` with `amount: 0` + the cell's `public_key`), so a
    /// brand-new client cell `derive_raw(pubkey, blake3("default"))` EXISTS before
    /// its first signed turn (a turn can't conjure its own agent cell). Returns the
    /// faucet's `success` truth. The faucet route is PUBLIC (no bearer) but requires
    /// the node be started with `--enable-faucet`. Mock returns `Ok(true)`.
    pub fn faucet_materialize(
        &self,
        recipient_hex: &str,
        public_key_hex: &str,
    ) -> anyhow::Result<bool> {
        match self {
            NodeClient::Mock => Ok(true),
            NodeClient::Http { base_url, .. } => {
                let body = serde_json::json!({
                    "recipient": recipient_hex,
                    "amount": 0u64,
                    "public_key": public_key_hex,
                });
                let resp: serde_json::Value = http_post_json(base_url, "/api/faucet", None, &body)?;
                Ok(resp
                    .get("success")
                    .and_then(serde_json::Value::as_bool)
                    .unwrap_or(false))
            }
        }
    }
}

/// Blocking JSON GET. The live shell drives reads on a background thread (the
/// `LiveNode` reader) so the gpui side stays single-threaded; the bare call is
/// kept blocking for clarity. Gated on `live-node` (the reqwest byte-pull); the
/// `Mock` arm above needs none of this, so a no-`live-node` build still has a
/// working `NodeClient::Mock`.
#[cfg(feature = "live-node")]
fn http_get<T: serde::de::DeserializeOwned>(base: &str, path: &str) -> anyhow::Result<T> {
    let url = format!("{base}{path}");
    let body = reqwest::blocking::get(&url)?.error_for_status()?.text()?;
    Ok(serde_json::from_str(&body)?)
}

/// Blocking JSON GET with an optional `Bearer` credential — the read twin of
/// [`http_post_json`] for routes the gateway gates on the ACCOUNT credential
/// (the `/v1/vats` roster: your fleet, resolved from your caps, nobody
/// else's). A non-2xx status folds the body text into the error so a 401 says
/// "missing/expired credential" rather than an opaque status code.
#[cfg(feature = "live-node")]
fn http_get_authed<T: serde::de::DeserializeOwned>(
    base: &str,
    path: &str,
    bearer: Option<&str>,
) -> anyhow::Result<T> {
    let url = format!("{base}{path}");
    let mut builder = reqwest::blocking::Client::new().get(&url);
    if let Some(token) = bearer {
        builder = builder.bearer_auth(token);
    }
    let resp = builder.send()?;
    let status = resp.status();
    let body = resp.text()?;
    if !status.is_success() {
        anyhow::bail!("GET {path} -> HTTP {status}: {body}");
    }
    Ok(serde_json::from_str(&body)?)
}

/// Blocking JSON POST returning a typed response, with an optional `Bearer`
/// operator token (the unlocked-node write credential `require_auth` checks).
///
/// The node reports turn refusals IN-BAND with a 200 body (`accepted: false`),
/// so we do NOT `error_for_status` on those — only a genuine transport/HTTP
/// failure (401/403/5xx) becomes an `Err`, with the body text folded in so a
/// 401 says "missing/expired operator token" rather than an opaque status.
#[cfg(feature = "live-node")]
fn http_post_json<T: serde::Serialize, R: serde::de::DeserializeOwned>(
    base: &str,
    path: &str,
    bearer: Option<&str>,
    req: &T,
) -> anyhow::Result<R> {
    let url = format!("{base}{path}");
    let mut builder = reqwest::blocking::Client::new().post(&url).json(req);
    if let Some(token) = bearer {
        builder = builder.bearer_auth(token);
    }
    let resp = builder.send()?;
    let status = resp.status();
    let body = resp.text()?;
    if !status.is_success() {
        anyhow::bail!("POST {path} -> HTTP {status}: {body}");
    }
    Ok(serde_json::from_str(&body)?)
}

/// Blocking OCTET-STREAM POST returning a typed JSON response, with an optional
/// `Bearer` operator token. The body is a raw `Vec<u8>` (a postcard-encoded
/// `SignedTurn`) sent as `application/octet-stream`.
///
/// Like [`http_post_json`], the node reports turn refusals IN-BAND with a 200 body
/// (`accepted: false`), so we do NOT `error_for_status` on a success — only a
/// genuine transport/HTTP failure (401/403/5xx) becomes an `Err`, with the body
/// text folded in.
#[cfg(feature = "live-node")]
fn http_post_octet<R: serde::de::DeserializeOwned>(
    base: &str,
    path: &str,
    bearer: Option<&str>,
    body: Vec<u8>,
) -> anyhow::Result<R> {
    let url = format!("{base}{path}");
    let mut builder = reqwest::blocking::Client::new()
        .post(&url)
        .header(reqwest::header::CONTENT_TYPE, "application/octet-stream")
        .body(body);
    if let Some(token) = bearer {
        builder = builder.bearer_auth(token);
    }
    let resp = builder.send()?;
    let status = resp.status();
    let text = resp.text()?;
    if !status.is_success() {
        anyhow::bail!("POST {path} -> HTTP {status}: {text}");
    }
    Ok(serde_json::from_str(&text)?)
}

// Without `live-node` (no reqwest), an `Http` arm can't reach the network. These
// stubs keep `NodeClient` compiling (the `Mock` backend stays fully functional);
// an `Http` call returns an honest "feature off" error rather than failing to
// build. (In practice both `native-full` and `sel4-thin` enable `live-node`.)
#[cfg(not(feature = "live-node"))]
fn http_get<T: serde::de::DeserializeOwned>(_base: &str, _path: &str) -> anyhow::Result<T> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

#[cfg(not(feature = "live-node"))]
fn http_get_authed<T: serde::de::DeserializeOwned>(
    _base: &str,
    _path: &str,
    _bearer: Option<&str>,
) -> anyhow::Result<T> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

#[cfg(not(feature = "live-node"))]
fn http_post_json<T: serde::Serialize, R: serde::de::DeserializeOwned>(
    _base: &str,
    _path: &str,
    _bearer: Option<&str>,
    _req: &T,
) -> anyhow::Result<R> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

#[cfg(not(feature = "live-node"))]
fn http_post_octet<R: serde::de::DeserializeOwned>(
    _base: &str,
    _path: &str,
    _bearer: Option<&str>,
    _body: Vec<u8>,
) -> anyhow::Result<R> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

/// In-process fixtures. These mirror the SHAPES a real node returns so the
/// views render against real data the moment a node is wired in.
pub mod mock {
    use super::*;

    pub fn status() -> NodeStatus {
        NodeStatus {
            healthy: true,
            peer_count: 3,
            latest_height: 142,
            dag_height: 1888,
            block_count: 1888,
            consensus_live: true,
            federation_mode: "sovereign".into(),
            public_key: "a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90".into(),
            state_producer: "lean".into(),
            lean_producer: true,
            full_turn_proving: true,
            producer_covered_effects: 51,
        }
    }

    pub fn cells() -> Vec<CellListEntry> {
        vec![
            CellListEntry {
                id: "11".repeat(32),
                balance: 100_000,
                nonce: 12,
                capability_count: 3,
                has_delegate: true,
                has_program: false,
                found: true,
            },
            CellListEntry {
                id: "22".repeat(32),
                balance: -500_000, // an issuer well: −supply
                nonce: 4,
                capability_count: 1,
                has_delegate: false,
                has_program: true,
                found: true,
            },
            CellListEntry {
                id: "33".repeat(32),
                balance: 7_500,
                nonce: 88,
                capability_count: 9,
                has_delegate: true,
                has_program: true,
                found: true,
            },
        ]
    }

    pub fn receipts() -> Vec<ReceiptEvent> {
        vec![
            ReceiptEvent {
                chain_index: 141,
                receipt_hash: "ab".repeat(32),
                turn_hash: "cd".repeat(32),
                cells: vec!["11".repeat(32), "33".repeat(32)],
                kinds: vec!["transfer".into(), "emit_event".into()],
                height: 1887,
                has_proof: true,
                finality: "final".into(),
                timestamp: 1_718_000_000,
            },
            ReceiptEvent {
                chain_index: 142,
                receipt_hash: "ef".repeat(32),
                turn_hash: "01".repeat(32),
                cells: vec!["22".repeat(32)],
                kinds: vec!["set_field".into()],
                height: 1888,
                has_proof: false,
                finality: "committed".into(),
                timestamp: 1_718_000_042,
            },
        ]
    }

    /// The `/v1/vats` roster fixture — three Dregg Computers in the three
    /// honest lifecycle postures the designed gateway reports (the SAME wire
    /// shape [`super::VATS_ROUTE`] will carry):
    ///
    ///   * **`mybox`** — RUNNING and reachable: an endpoint to attach to,
    ///     funded, three periods settled, full (proof-as-you-go) witnessing.
    ///   * **`nightshift`** — SLEEPING as a cell: no endpoint (nothing is
    ///     listening), but a committed `checkpoint_root` it wakes from — the
    ///     computer IS its commitment while it sleeps. Symbolic (cheap,
    ///     verify-later) witnessing.
    ///   * **`scratch`** — CREATED but never funded: the admission gate read
    ///     the reserve and refused to launch. No endpoint, no periods — the
    ///     roster shows it honestly rather than pretending a machine exists.
    pub fn vats() -> Vec<VatEntry> {
        vec![
            VatEntry {
                cell_id: "dc".repeat(32),
                name: "mybox".into(),
                owner: "acct:renter".into(),
                endpoint: Some("http://127.0.0.1:8730".into()),
                state: "running".into(),
                funded: true,
                paid_periods: 3,
                checkpoint_root: None,
                witness_mode: "full".into(),
            },
            VatEntry {
                cell_id: "5e".repeat(32),
                name: "nightshift".into(),
                owner: "acct:renter".into(),
                endpoint: None,
                state: "sleeping".into(),
                funded: true,
                paid_periods: 12,
                checkpoint_root: Some("9a".repeat(32)),
                witness_mode: "symbolic".into(),
            },
            VatEntry {
                cell_id: "7a".repeat(32),
                name: "scratch".into(),
                owner: "acct:renter".into(),
                endpoint: None,
                state: "created".into(),
                funded: false,
                paid_periods: 0,
                checkpoint_root: None,
                witness_mode: "full".into(),
            },
        ]
    }

    pub fn federations() -> Vec<FederationInfo> {
        vec![FederationInfo {
            id: "local".into(),
            federation_id: "f0".repeat(32),
            committee_epoch: 7,
            threshold: 3,
            member_count: 5,
            members: (0..5).map(|i| format!("{:02x}", i).repeat(32)).collect(),
            is_local: true,
            latest_height: 142,
            latest_root: Some("9a".repeat(32)),
            num_finalized_roots: 142,
        }]
    }

    pub fn blocks() -> Vec<BlockInfo> {
        (1880..1888)
            .rev()
            .map(|h| BlockInfo {
                height: h,
                hash: format!("{h:04x}").repeat(16),
                creator: "11".repeat(32),
                seq: h,
            })
            .collect()
    }

    /// A demo turn the TurnComposer view starts from.
    pub fn sample_turn() -> SubmitTurnRequest {
        SubmitTurnRequest {
            agent: "11".repeat(32),
            nonce: 13,
            fee: 1,
            memo: Some("starbridge-v2 demo turn".into()),
            actions: vec![TurnActionSpec {
                target: Some("33".repeat(32)),
                method: Some("submit".into()),
                effects: vec![
                    TurnEffectSpec::Transfer {
                        from: Some("11".repeat(32)),
                        to: "33".repeat(32),
                        amount: 250,
                    },
                    TurnEffectSpec::EmitEvent {
                        cell: None,
                        topic: "greeting".into(),
                        data: vec!["0x01".into()],
                    },
                ],
            }],
        }
    }
}

// ===========================================================================
// THE LIVE NODE CONNECTION — snapshot sync + the background SSE reader.
//
// This is the I/O driver the embedded master interface's LIVE-NODE panel owns. It
// pairs a [`NodeClient`] with the live-reflection model (`crate::live_node`):
//   * `sync()` does the blocking snapshot reads (`/status`, `/api/cells`,
//     `/api/receipts`) and projects them into the uniform `Inspectable` model.
//   * `connect_stream()` spawns a BACKGROUND THREAD that pulls the
//     `/api/events/stream` SSE socket and feeds each chunk into the PURE
//     `SseParser`, pushing decoded receipts onto an mpsc channel. The cockpit owns
//     the receiver and drains it each frame under `cx.notify()` — so the gpui side
//     stays single-threaded and the ReceiptInspector advances LIVE (per receipt),
//     replacing the static snapshot. The reader auto-reconnects, resuming from the
//     `Last-Event-ID` cursor the channel's consumer reports back.
//
// The pure parse/reflect/feed live in `crate::live_node` (tested with byte
// fixtures, no socket); this is only the byte source + the thread plumbing.
// ===========================================================================

/// A live connection to a node: a [`NodeClient`] plus the reflection model. The
/// snapshot sync is always available (the byte-pull is `live-node`-gated inside
/// `http_get`); the SSE reader is `connect_stream`.
#[cfg(feature = "embedded-executor")]
pub struct LiveNode {
    client: NodeClient,
}

#[cfg(feature = "embedded-executor")]
impl LiveNode {
    /// Wrap a client (typically `NodeClient::http(base_url)`).
    pub fn new(client: NodeClient) -> Self {
        LiveNode { client }
    }

    /// The underlying client (for the writes surface / describe).
    pub fn client(&self) -> &NodeClient {
        &self.client
    }

    /// Blocking SNAPSHOT sync: fetch `/status` + `/api/cells` and project them
    /// into the uniform reflective model. Returns the node's status reflection +
    /// one cell reflection per live cell (the inspector renders these identically
    /// to embedded-world cells — no parallel view path). Errors propagate (an
    /// unreachable node surfaces honestly).
    ///
    /// The cockpit calls this off the gpui thread (or on a one-shot button) and
    /// re-renders from the result; the per-receipt LIVE updates come from
    /// [`LiveNode::connect_stream`], not this.
    pub fn sync(&self) -> anyhow::Result<LiveSnapshot> {
        let status = self.client.status()?;
        let cells = self.client.cells()?;
        let status_view =
            crate::live_node::LiveReflection::reflect_status(&self.client.describe(), &status);
        let cell_views = cells
            .iter()
            .map(crate::live_node::LiveReflection::reflect_cell_entry)
            .collect();
        Ok(LiveSnapshot {
            status,
            status_view,
            cell_views,
        })
    }

    /// Spawn the BACKGROUND SSE READER (the live receipt nervous-system tap).
    ///
    /// Returns a [`ReceiptStreamHandle`]: the cockpit holds the `rx` and drains it
    /// each frame (each drained [`ReceiptEvent`] is a `cx.notify()`). The reader
    /// thread pulls `/api/events/stream`, feeds chunks into the pure
    /// [`crate::live_node::SseParser`], and auto-reconnects (resuming from the last
    /// delivered chain index) until the receiver is dropped. `None` for a mock
    /// backend (no stream) or when `live-node` is off.
    #[cfg(feature = "live-node")]
    pub fn connect_stream(&self) -> Option<ReceiptStreamHandle> {
        // Only an Http backend has a stream; the reader rebuilds the URL itself
        // (and sets the Last-Event-ID resume header) per connect attempt.
        let base = match &self.client {
            NodeClient::Http { base_url, .. } => base_url.clone(),
            NodeClient::Mock => return None,
        };
        let (tx, rx) = std::sync::mpsc::channel::<crate::live_node::SseRecord>();
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let stop_reader = stop.clone();
        let handle = std::thread::Builder::new()
            .name("starbridge-sse".into())
            .spawn(move || sse_reader_loop(base, tx, stop_reader))
            .ok()?;
        Some(ReceiptStreamHandle {
            rx,
            stop,
            _join: Some(handle),
        })
    }

    /// On a non-`live-node` build there is no reader; the panel falls back to the
    /// snapshot (`sync`) or the mock.
    #[cfg(not(feature = "live-node"))]
    pub fn connect_stream(&self) -> Option<ReceiptStreamHandle> {
        None
    }
}

/// A blocking snapshot of a live node, projected into the uniform reflective
/// model (the inspector renders these the same as embedded-world objects).
#[cfg(feature = "embedded-executor")]
pub struct LiveSnapshot {
    /// The raw status (for the header / producer badge).
    pub status: NodeStatus,
    /// The status reflection (the distribution-axis object).
    pub status_view: crate::reflect::Inspectable,
    /// One reflection per live cell.
    pub cell_views: Vec<crate::reflect::Inspectable>,
}

/// The handle the cockpit holds onto a running SSE reader. Dropping it signals the
/// reader thread to stop (the next read/reconnect observes the flag and exits).
#[cfg(feature = "embedded-executor")]
pub struct ReceiptStreamHandle {
    /// Decoded receipts as they stream in — the cockpit drains this each frame and
    /// fires a `cx.notify()` per record. Empty (would-block) between commits.
    pub rx: std::sync::mpsc::Receiver<crate::live_node::SseRecord>,
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// The reader thread join handle (joined on drop, best-effort).
    _join: Option<std::thread::JoinHandle<()>>,
}

#[cfg(feature = "embedded-executor")]
impl ReceiptStreamHandle {
    /// Non-blocking drain of every record that arrived since the last call. The
    /// cockpit calls this each frame; each returned record is one `cx.notify()`.
    pub fn drain(&self) -> Vec<crate::live_node::SseRecord> {
        self.rx.try_iter().collect()
    }
}

#[cfg(feature = "embedded-executor")]
impl Drop for ReceiptStreamHandle {
    fn drop(&mut self) {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(h) = self._join.take() {
            // Best-effort: the reader observes `stop` on its next read boundary.
            // We don't block shutdown on a slow socket — detach if it lingers.
            let _ = h;
        }
    }
}

/// The background SSE reader loop: pull `/api/events/stream`, feed the pure
/// parser, push decoded receipts onto `tx`, and reconnect (resuming from the last
/// delivered chain index) until `stop` is set or the receiver is gone.
#[cfg(all(feature = "embedded-executor", feature = "live-node"))]
fn sse_reader_loop(
    base_url: String,
    tx: std::sync::mpsc::Sender<crate::live_node::SseRecord>,
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
) {
    use std::io::Read;
    use std::sync::atomic::Ordering;

    let client = NodeClient::http(&base_url);
    let mut resume: Option<u64> = None;
    while !stop.load(Ordering::Relaxed) {
        // The stream URL (no resume in the query — the node resumes from the
        // `Last-Event-ID` HEADER, which is the protocol's mechanism per
        // `node/src/events.rs`; we set that header below from `resume`).
        let Some(url) = client.events_stream_url(None) else {
            return;
        };
        // A long-lived streaming GET. reqwest blocking returns a `Response` whose
        // body we read in chunks (the stream stays open; reads block until the
        // node sends the next receipt or a heartbeat). On a RECONNECT we send
        // `Last-Event-ID: <resume>` so the node tails AFTER the last delivered
        // chain index (at-least-once across reconnects; the feed dedups).
        let mut req = match reqwest::blocking::Client::builder()
            .timeout(None) // no overall timeout — it's a long-lived stream
            .build()
        {
            Ok(c) => c.get(&url),
            Err(_) => {
                if backoff_or_stop(&stop) {
                    return;
                }
                continue;
            }
        };
        if let Some(id) = resume {
            req = req.header("Last-Event-ID", id.to_string());
        }
        let resp = match req.send() {
            Ok(r) => r,
            Err(_) => {
                // Connection failed — back off and retry (resuming from `resume`).
                if backoff_or_stop(&stop) {
                    return;
                }
                continue;
            }
        };
        let mut resp = resp;
        let mut parser = crate::live_node::SseParser::new();
        let mut chunk = [0u8; 4096];
        loop {
            if stop.load(Ordering::Relaxed) {
                return;
            }
            match resp.read(&mut chunk) {
                Ok(0) => break, // server closed — reconnect (resume cursor held)
                Ok(n) => {
                    for rec in parser.push(&chunk[..n]) {
                        if let Some(id) = rec.id {
                            resume = Some(id);
                        }
                        // The receiver was dropped (cockpit closed the panel) —
                        // stop the reader.
                        if tx.send(rec).is_err() {
                            return;
                        }
                    }
                }
                Err(_) => break, // read error — reconnect
            }
        }
        if backoff_or_stop(&stop) {
            return;
        }
    }
}

/// Sleep a short reconnect backoff in small steps, checking `stop` so a dropped
/// handle shuts the reader down promptly. Returns `true` if `stop` was observed
/// (the caller should return).
#[cfg(all(feature = "embedded-executor", feature = "live-node"))]
fn backoff_or_stop(stop: &std::sync::atomic::AtomicBool) -> bool {
    use std::sync::atomic::Ordering;
    for _ in 0..10 {
        if stop.load(Ordering::Relaxed) {
            return true;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    false
}
